/*
 * Stream filters related variables and functions.
 *
 * Copyright (C) 2024 AVEST plc, Maxim Kostyshin <maxk@avest.by>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version
 * 2 of the License, or (at your option) any later version.
 *
 */

#include <ctype.h>

#include <haproxy/api.h>
#include <haproxy/channel-t.h>
#include <haproxy/errors.h>
#include <haproxy/filters.h>
#include <haproxy/global.h>
#include <haproxy/http_ana-t.h>
#include <haproxy/http_htx.h>
#include <haproxy/htx.h>
#include <haproxy/proxy-t.h>
#include <haproxy/stream.h>
#include <haproxy/time.h>
#include <haproxy/tools.h>

#define SIGNATURE_UNIQ (const char *)"AVTLSPROXY"

const char *placemark_flt_id = "placemark filter";

struct flt_ops placemark_ops;

#define PLACEMARK_F_QUIET         0x00000001
#define PLACEMARK_F_MODIFY_PACKET 0x00000002 // Av
#define PLACEMARK_F_HEXDUMP       0x00000004

struct placemark_config {
	struct proxy *proxy;
	char         *name;
	char         *label; // Av
	unsigned int  flags;
};

#define FLT_PLACEMARK(conf, fmt, ...)						\
	do {									\
		if (!(conf->flags & PLACEMARK_F_QUIET))				\
			fprintf(stderr, "%d.%06d [%-20s] " fmt "\n",		\
				(int)date.tv_sec, (int)date.tv_usec, (conf)->name,\
				##__VA_ARGS__);					\
	} while (0)

#define FLT_STRM_PLACEMARK(conf, strm, fmt, ...)								\
	do {												\
		if (!(conf->flags & PLACEMARK_F_QUIET))							\
			fprintf(stderr, "%d.%06d [%-20s] [strm %p(%x) 0x%08x 0x%08x] " fmt "\n",	\
				(int)date.tv_sec, (int)date.tv_usec, (conf)->name,			\
				strm, (strm ? ((struct stream *)strm)->uniq_id : ~0U),			\
				(strm ? strm->req.analysers : 0), (strm ? strm->res.analysers : 0),	\
				##__VA_ARGS__);								\
	} while (0)


static const char *
channel_label(const struct channel *chn)
{
	return (chn->flags & CF_ISRESP) ? "RESPONSE" : "REQUEST";
}

static const char *
proxy_mode(const struct stream *s)
{
	struct proxy *px = (s->flags & SF_BE_ASSIGNED ? s->be : strm_fe(s));

	return ((px->mode == PR_MODE_HTTP) ? "HTTP" : "TCP");
}

static const char *
stream_pos(const struct stream *s)
{
	return (s->flags & SF_BE_ASSIGNED) ? "backend" : "frontend";
}

static const char *
filter_type(const struct filter *f)
{
	return (f->flags & FLT_FL_IS_BACKEND_FILTER) ? "backend" : "frontend";
}

static void
placemark_hexdump(struct ist ist)
{
	int i, j, padding;

	padding = ((ist.len % 16) ? (16 - ist.len % 16) : 0);
	for (i = 0; i < ist.len + padding; i++) {
                if (!(i % 16))
                        fprintf(stderr, "\t0x%06x: ", i);
		else if (!(i % 8))
                        fprintf(stderr, "  ");

                if (i < ist.len)
                        fprintf(stderr, "%02x ", (unsigned char)*(ist.ptr+i));
                else
                        fprintf(stderr, "   ");

                /* print ASCII dump */
                if (i % 16 == 15) {
                        fprintf(stderr, "  |");
                        for(j = i - 15; j <= i && j < ist.len; j++)
				fprintf(stderr, "%c", (isprint((unsigned char)*(ist.ptr+j)) ? *(ist.ptr+j) : '.'));
                        fprintf(stderr, "|\n");
                }
        }
}

static void
placemark_raw_hexdump(struct buffer *buf, unsigned int offset, unsigned int len)
{
	unsigned char p[len];
	int block1, block2;

	block1 = len;
	if (block1 > b_contig_data(buf, offset))
		block1 = b_contig_data(buf, offset);
	block2 = len - block1;

	memcpy(p, b_peek(buf, offset), block1);
	memcpy(p+block1, b_orig(buf), block2);
	placemark_hexdump(ist2(p, len));
}

static void
placemark_htx_hexdump(struct htx *htx, unsigned int offset, unsigned int len)
{
	struct htx_blk *blk;

	for (blk = htx_get_first_blk(htx); blk && len; blk = htx_get_next_blk(htx, blk)) {
		enum htx_blk_type type = htx_get_blk_type(blk);
		uint32_t sz = htx_get_blksz(blk);
		struct ist v;

		if (offset >= sz) {
			offset -= sz;
			continue;
		}

		v = htx_get_blk_value(htx, blk);
		v = istadv(v, offset);
		offset = 0;

		v = isttrim(v, len);
		len -= v.len;
		if (type == HTX_BLK_DATA)
			placemark_hexdump(v);
	}
}

static unsigned int
placemark_get_htx_datalen(struct htx *htx, unsigned int offset, unsigned int len)
{
	struct htx_blk *blk;
	struct htx_ret htxret = htx_find_offset(htx, offset);
	uint32_t data = 0;

	blk = htxret.blk;
	if (blk && htxret.ret && htx_get_blk_type(blk) == HTX_BLK_DATA) {
		data += htxret.ret;
		blk = htx_get_next_blk(htx, blk);
	}
	while (blk) {
		if (htx_get_blk_type(blk) == HTX_BLK_UNUSED)
			goto next;
		else if (htx_get_blk_type(blk) != HTX_BLK_DATA)
			break;
		data += htx_get_blksz(blk);
	  next:
		blk = htx_get_next_blk(htx, blk);
	}
	return data;
}

/***************************************************************************
 * Hooks that manage the filter lifecycle (init/check/deinit)
 **************************************************************************/
/* Initialize the filter. Returns -1 on error, else 0. */
static int
placemark_init(struct proxy *px, struct flt_conf *fconf)
{
	struct placemark_config *conf = fconf->conf;

	if (conf->name)
		memprintf(&conf->name, "%s/%s", conf->name, px->id);
	else
		memprintf(&conf->name, "PLACEMARK/%s", px->id);

	fconf->flags |= FLT_CFG_FL_HTX;
	fconf->conf = conf;

	FLT_PLACEMARK(conf, "filter initialized [quiet=%s - label=%s - modify packet=%s - hexdump=%s]",
		  ((conf->flags & PLACEMARK_F_QUIET) ? "true" : "false"),
		  (conf->label),
		  ((conf->flags & PLACEMARK_F_MODIFY_PACKET) ? "true" : "false"),
		  ((conf->flags & PLACEMARK_F_HEXDUMP) ? "true" : "false"));
	return 0;
}

/* Free resources allocated by the placemark filter. */
static void
placemark_deinit(struct proxy *px, struct flt_conf *fconf)
{
	struct placemark_config *conf = fconf->conf;

	if (conf) {
		FLT_PLACEMARK(conf, "filter deinitialized");
		free(conf->name);
		free(conf->label); // Av
		free(conf);
	}
	fconf->conf = NULL;
}

/* Check configuration of a placemark filter for a specified proxy.
 * Return 1 on error, else 0. */
static int
placemark_check(struct proxy *px, struct flt_conf *fconf)
{
	return 0;
}

/* Initialize the filter for each thread. Return -1 on error, else 0. */
static int
placemark_init_per_thread(struct proxy *px, struct flt_conf *fconf)
{
	struct placemark_config *conf = fconf->conf;

	FLT_PLACEMARK(conf, "filter initialized for thread tid %u", tid);
	return 0;
}

/* Free resources allocate by the placemark filter for each thread. */
static void
placemark_deinit_per_thread(struct proxy *px, struct flt_conf *fconf)
{
	struct placemark_config *conf = fconf->conf;

	if (conf)
		FLT_PLACEMARK(conf, "filter deinitialized for thread tid %u", tid);
}

/**************************************************************************
 * Hooks to handle start/stop of streams
 *************************************************************************/
/* Called when a filter instance is created and attach to a stream */
static int
placemark_attach(struct stream *s, struct filter *filter)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s: filter-type=%s",
		   __FUNCTION__, filter_type(filter));

	return 1;
}

/* Called when a filter instance is detach from a stream, just before its
 * destruction */
static void
placemark_detach(struct stream *s, struct filter *filter)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s: filter-type=%s",
		   __FUNCTION__, filter_type(filter));
}

/* Called when a stream is created */
static int
placemark_stream_start(struct stream *s, struct filter *filter)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s",
		   __FUNCTION__);
	return 0;
}


/* Called when a backend is set for a stream */
static int
placemark_stream_set_backend(struct stream *s, struct filter *filter,
			 struct proxy *be)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s: backend=%s",
		   __FUNCTION__, be->id);
	return 0;
}

/* Called when a stream is destroyed */
static void
placemark_stream_stop(struct stream *s, struct filter *filter)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s",
		   __FUNCTION__);
}

/* Called when the stream is woken up because of an expired timer */
static void
placemark_check_timeouts(struct stream *s, struct filter *filter)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s",
		   __FUNCTION__);
}

/**************************************************************************
 * Hooks to handle channels activity
 *************************************************************************/
/* Called when analyze starts for a given channel */
static int
placemark_chn_start_analyze(struct stream *s, struct filter *filter,
			struct channel *chn)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s: channel=%-10s - mode=%-5s (%s)",
		   __FUNCTION__,
		   channel_label(chn), proxy_mode(s), stream_pos(s));
	filter->pre_analyzers  |= (AN_REQ_ALL | AN_RES_ALL);
	filter->post_analyzers |= (AN_REQ_ALL | AN_RES_ALL);
	register_data_filter(s, chn, filter);
	return 1;
}

/* Called before a processing happens on a given channel */
static int
placemark_chn_analyze(struct stream *s, struct filter *filter,
		  struct channel *chn, unsigned an_bit)
{
	struct placemark_config *conf = FLT_CONF(filter);
	char                *ana;

	switch (an_bit) {
		case AN_REQ_INSPECT_FE:
			ana = "AN_REQ_INSPECT_FE";
			break;
		case AN_REQ_WAIT_HTTP:
			ana = "AN_REQ_WAIT_HTTP";
			break;
		case AN_REQ_HTTP_BODY:
			ana = "AN_REQ_HTTP_BODY";
			break;
		case AN_REQ_HTTP_PROCESS_FE:
			ana = "AN_REQ_HTTP_PROCESS_FE";
			break;
		case AN_REQ_SWITCHING_RULES:
			ana = "AN_REQ_SWITCHING_RULES";
			break;
		case AN_REQ_INSPECT_BE:
			ana = "AN_REQ_INSPECT_BE";
			break;
		case AN_REQ_HTTP_PROCESS_BE:
			ana = "AN_REQ_HTTP_PROCESS_BE";
			break;
		case AN_REQ_SRV_RULES:
			ana = "AN_REQ_SRV_RULES";
			break;
		case AN_REQ_HTTP_INNER:
			ana = "AN_REQ_HTTP_INNER";
			break;
		case AN_REQ_HTTP_TARPIT:
			ana = "AN_REQ_HTTP_TARPIT";
			break;
		case AN_REQ_STICKING_RULES:
			ana = "AN_REQ_STICKING_RULES";
			break;
		case AN_REQ_PRST_RDP_COOKIE:
			ana = "AN_REQ_PRST_RDP_COOKIE";
			break;
		case AN_REQ_HTTP_XFER_BODY:
			ana = "AN_REQ_HTTP_XFER_BODY";
			break;
		case AN_RES_INSPECT:
			ana = "AN_RES_INSPECT";
			break;
		case AN_RES_WAIT_HTTP:
			ana = "AN_RES_WAIT_HTTP";
			break;
		case AN_RES_HTTP_PROCESS_FE: // AN_RES_HTTP_PROCESS_BE
			ana = "AN_RES_HTTP_PROCESS_FE/BE";
			break;
		case AN_RES_STORE_RULES:
			ana = "AN_RES_STORE_RULES";
			break;
		case AN_RES_HTTP_XFER_BODY:
			ana = "AN_RES_HTTP_XFER_BODY";
			break;
		default:
			ana = "unknown";
	}

	FLT_STRM_PLACEMARK(conf, s, "%-25s: channel=%-10s - mode=%-5s (%s) - "
		   "analyzer=%s - step=%s",
		   __FUNCTION__,
		   channel_label(chn), proxy_mode(s), stream_pos(s),
		   ana, ((chn->analysers & an_bit) ? "PRE" : "POST"));
	return 1;
}

/* Called when analyze ends for a given channel */
static int
placemark_chn_end_analyze(struct stream *s, struct filter *filter,
		      struct channel *chn)
{
	struct placemark_config *conf = FLT_CONF(filter);

	FLT_STRM_PLACEMARK(conf, s, "%-25s: channel=%-10s - mode=%-5s (%s)",
		   __FUNCTION__,
		   channel_label(chn), proxy_mode(s), stream_pos(s));
	return 1;
}

/**************************************************************************
 * Hooks to filter TCP data
 *************************************************************************/
static int
placemark_tcp_payload(struct stream *s, struct filter *filter, struct channel *chn,
		  unsigned int offset, unsigned int len)
{
	struct placemark_config *conf = FLT_CONF(filter);
	int ret = len;

	if (s->flags & SF_HTX) {
	if (ret && (conf->flags & PLACEMARK_F_HEXDUMP)) {
		FLT_STRM_PLACEMARK(conf, s, "%-25s: channel=%-10s - mode=%-5s (%s) - "
			       "offset=%u - len=%u - forward=%d",
			       __FUNCTION__,
			       channel_label(chn), proxy_mode(s), stream_pos(s),
			       offset, len, ret);


		placemark_htx_hexdump(htxbuf(&chn->buf), offset, ret);
	}
	}
	else {
		if (ret && (conf->flags & PLACEMARK_F_HEXDUMP)) {
			FLT_STRM_PLACEMARK(conf, s, "%-25s: channel=%-10s - mode=%-5s (%s) - "
				"offset=%u - len=%u - forward=%d",
			    __FUNCTION__,
			    channel_label(chn), proxy_mode(s), stream_pos(s),
			    offset, len, ret);
			placemark_raw_hexdump(&chn->buf, offset, ret);
		}

		if (ret && (conf->flags & PLACEMARK_F_MODIFY_PACKET) && len >= strlen(conf->label) &&
			strstr((&chn->buf)->area, conf->label) == (&chn->buf)->area ) {
			for(int i=strlen(conf->label); i<len; i++)
			       ((&chn->buf)->area)[i-strlen(conf->label)] = ((&chn->buf)->area)[i];
			for(int i=len-strlen(conf->label); i<len; i++)
			       ((&chn->buf)->area)[i] = 0x0;
			(&chn->buf)->data = (&chn->buf)->data - (size_t)strlen(conf->label);
			ret = ret - strlen(conf->label);
			if (conf->flags & PLACEMARK_F_HEXDUMP)
			       placemark_raw_hexdump(&chn->buf, offset, ret);
		}
	}

	if (ret != len) {
		 flt_update_offsets(filter, chn, ret - len); // Av
		 task_wakeup(s->task, TASK_WOKEN_MSG);
	}
	return ret;
}
/********************************************************************
 * Functions that manage the filter initialization
 ********************************************************************/
struct flt_ops placemark_ops = {
	/* Manage placemark filter, called for each filter declaration */
	.init              = placemark_init,
	.deinit            = placemark_deinit,
	.check             = placemark_check,
	.init_per_thread   = placemark_init_per_thread,
	.deinit_per_thread = placemark_deinit_per_thread,

	/* Handle start/stop of streams */
	.attach             = placemark_attach,
	.detach             = placemark_detach,
	.stream_start       = placemark_stream_start,
	.stream_set_backend = placemark_stream_set_backend,
	.stream_stop        = placemark_stream_stop,
	.check_timeouts     = placemark_check_timeouts,

	/* Handle channels activity */
	.channel_start_analyze = placemark_chn_start_analyze,
	.channel_pre_analyze   = placemark_chn_analyze,
	.channel_post_analyze  = placemark_chn_analyze,
	.channel_end_analyze   = placemark_chn_end_analyze,

	/* Filter TCP data */
	.tcp_payload        = placemark_tcp_payload,
};

/* Return -1 on error, else 0 */
static int
parse_placemark_flt(char **args, int *cur_arg, struct proxy *px,
                struct flt_conf *fconf, char **err, void *private)
{
	struct placemark_config *conf;
	int                  pos = *cur_arg;

	conf = calloc(1, sizeof(*conf));
	if (!conf) {
		memprintf(err, "%s: out of memory", args[*cur_arg]);
		return -1;
	}
	conf->proxy = px;
	conf->flags = 0;
	if (strcmp(args[pos], "placemark") == 0) {
		pos++;

		while (*args[pos]) {
			if (strcmp(args[pos], "name") == 0) {
				if (!*args[pos + 1]) {
					memprintf(err, "'%s' : '%s' option without value",
						  args[*cur_arg], args[pos]);
					goto error;
				}
				conf->name = strdup(args[pos + 1]);
				if (!conf->name) {
					memprintf(err, "%s: out of memory", args[*cur_arg]);
					goto error;
				}
				pos++;
			}
//			else if (strcmp(args[pos], "quiet") == 0) // Av, see hexdump
//				conf->flags |= PLACEMARK_F_QUIET;
			else if (strcmp(args[pos], "label") == 0) { // Av
				if (!*args[pos + 1]) {
					memprintf(err, "'%s' : '%s' option without value",
						  args[*cur_arg], args[pos]);
					goto error;
				}
				conf->label = strdup(args[pos + 1]);
				if (!conf->label) {
					memprintf(err, "%s: out of memory", args[*cur_arg]);
					goto error;
				}
				pos++;
			}
			else if (strcmp(args[pos], "remove-label") == 0) // Av
				conf->flags |= PLACEMARK_F_MODIFY_PACKET;
			else if (strcmp(args[pos], "hexdump") == 0) { // Av
				conf->flags |= PLACEMARK_F_HEXDUMP;
			}
			else
				break;
			pos++;
		}
		*cur_arg = pos;
		fconf->id   = placemark_flt_id;
		fconf->ops  = &placemark_ops;
	}

	if (!(conf->flags & PLACEMARK_F_HEXDUMP)) // Av
		conf->flags |= PLACEMARK_F_QUIET;
	
	if (!(conf->label)) { // Av
		conf->label = strdup(SIGNATURE_UNIQ);
		if (!conf->label) {
		    memprintf(err, "label: out of memory");
    		    goto error;
		}
	}

	fconf->conf = conf;
	return 0;

 error:
	if (conf->name)
		free(conf->name);
	if (conf->label)
		free(conf->label);
	free(conf);
	return -1;
}

/* Declare the filter parser for "placemark" keyword */
static struct flt_kw_list flt_kws = { "PLACEMARK", { }, {
		{ "placemark", parse_placemark_flt, NULL },
		{ NULL, NULL, NULL },
	}
};

INITCALL1(STG_REGISTER, flt_register_keywords, &flt_kws);

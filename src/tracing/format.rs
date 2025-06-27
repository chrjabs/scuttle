use owo_colors::OwoColorize;
use tracing::Event;
use tracing_subscriber::{
    fmt::{FmtContext, FormatEvent, FormatFields, format::Writer},
    registry::LookupSpan,
};

use super::{Styles, spans::SpanData};

pub struct Format {
    start_time: std::time::Instant,
    opts: Options,
}

impl Format {
    pub fn new(opts: Options) -> Self {
        Format {
            start_time: std::time::Instant::now(),
            opts,
        }
    }

    fn format_timestamp(&self, writer: &mut Writer<'_>, styles: &Styles) -> std::fmt::Result {
        if !self.opts.timestamps {
            return Ok(());
        }
        let elapsed = self.start_time.elapsed();
        write!(
            writer,
            "{}{:>8.3}{} ",
            "[".style(styles.timestamp),
            elapsed.as_secs_f64().style(styles.timestamp),
            "]".style(styles.timestamp)
        )
    }
}

impl<S, N> FormatEvent<S, N> for Format
where
    S: tracing::Subscriber + for<'a> LookupSpan<'a>,
    N: for<'a> FormatFields<'a> + 'static,
{
    fn format_event(
        &self,
        ctx: &FmtContext<'_, S, N>,
        mut writer: Writer<'_>,
        event: &Event<'_>,
    ) -> std::fmt::Result {
        let styles = if writer.has_ansi_escapes() {
            Styles::colored()
        } else {
            Styles::plain()
        };
        let meta = event.metadata();
        self.format_timestamp(&mut writer, &styles)?;
        // Indent based on scope depth
        if let Some(scope) = ctx.event_scope() {
            let mut scope_depth = scope.from_root().count();
            if meta.is_span() {
                scope_depth -= 1;
            }
            for _ in 0..scope_depth {
                write!(writer, " ")?;
            }
        }
        if meta.is_span() {
            let id = event.parent().expect("span event must have parent");
            let span = ctx.span(id).expect("parent of event must exist");
            let span_data = *span
                .extensions()
                .get::<SpanData>()
                .expect("must use spans layer");
            if span_data.inside {
                write!(writer, "{}", "[".style(styles.span_symb(meta.level())))?;
            } else {
                write!(writer, "{}", "]".style(styles.span_symb(meta.level())))?;
            }
            write!(
                writer,
                "{}",
                meta.name().style(styles.span_name(meta.level()))
            )?;
            if span_data.inside {
                let ext = span.extensions();
                if let Some(fields) = &ext.get::<tracing_subscriber::fmt::FormattedFields<N>>()
                    && !fields.is_empty()
                {
                    write!(writer, " {fields}")?;
                }
            } else {
                write!(
                    writer,
                    " {:.3}{}",
                    span_data
                        .start_time
                        .elapsed()
                        .as_secs_f64()
                        .style(styles.span_time),
                    " s".style(styles.span_time)
                )?;
            }
        } else {
            write!(
                writer,
                "{}",
                meta.target().style(styles.event_name(meta.level()))
            )?;
            if !meta.fields().is_empty() {
                write!(writer, " ")?;
                ctx.format_fields(writer.by_ref(), event)?;
            }
        }
        writeln!(writer)
    }
}

pub struct Options {
    timestamps: bool,
}

impl From<super::Options> for Options {
    fn from(value: super::Options) -> Self {
        Options {
            timestamps: value.timestamps,
        }
    }
}

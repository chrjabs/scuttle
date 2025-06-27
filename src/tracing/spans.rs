use tracing::{Subscriber, span::Id};
use tracing_subscriber::{Layer, layer::Context, registry::LookupSpan};

pub struct Spans;

impl<S> Layer<S> for Spans
where
    S: Subscriber,
    S: for<'lookup> LookupSpan<'lookup>,
{
    fn on_enter(&self, id: &Id, ctx: Context<'_, S>) {
        let span = ctx.span(id).unwrap();
        span.extensions_mut().insert(SpanData {
            start_time: std::time::Instant::now(),
            inside: true,
        })
    }

    fn on_exit(&self, id: &Id, ctx: Context<'_, S>) {
        let span = ctx.span(id).unwrap();
        span.extensions_mut().get_mut::<SpanData>().unwrap().inside = false;
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SpanData {
    pub start_time: std::time::Instant,
    pub inside: bool,
}

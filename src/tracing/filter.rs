use tracing::{Level, Metadata, Subscriber, subscriber::Interest};
use tracing_subscriber::{Layer, registry::LookupSpan};

pub struct Filter {
    opts: Options,
}

impl Filter {
    pub fn new(opts: Options) -> Self {
        Filter { opts }
    }
}

impl<S> Layer<S> for Filter
where
    S: Subscriber,
    S: for<'lookup> LookupSpan<'lookup>,
{
    fn register_callsite(&self, metadata: &'static Metadata<'static>) -> Interest {
        let name = metadata.name();
        if self.opts.candidates && name == "candidate" {
            return Interest::always();
        }
        if self.opts.solutions && name == "solution" {
            return Interest::always();
        }
        if self.opts.non_dominated && name == "non_dominated" {
            return Interest::always();
        }
        if self.opts.oracle_calls && name == "oracle_call" {
            return Interest::always();
        }
        if self.opts.oracle_calls && name == "oracle_call" {
            return Interest::always();
        }
        if self.opts.bound_points && (name == "ideal" || name == "nadir") {
            return Interest::always();
        }
        if *metadata.level() <= self.opts.level {
            return Interest::always();
        }
        Interest::never()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Options {
    candidates: bool,
    solutions: bool,
    non_dominated: bool,
    oracle_calls: bool,
    bound_points: bool,
    level: Level,
}

impl From<super::Options> for Options {
    fn from(value: super::Options) -> Self {
        Options {
            candidates: value.candidates,
            solutions: value.solutions,
            non_dominated: value.non_dominated,
            oracle_calls: value.oracle_calls,
            bound_points: value.bound_points,
            level: value.level,
        }
    }
}

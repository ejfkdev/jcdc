//! One accessor for the string payloads jdc-core 0.2 hands around.
//!
//! 0.2 made the IR payloads `Arc<str>` (cheap clones) while this front-end
//! still builds and reads plain `String`s. Comparing the two, or comparing
//! two `Arc<str>`s, has no `PartialEq` impl — and `str::as_str()` is
//! unstable, so `x.as_str()` on an `Arc<str>` does not resolve either.
//! `jstr()` is the single, type-inferable bridge used at those boundaries.
//!
//! Keep this thin: it exists so the migration diff stays mechanical, not as
//! an abstraction to build on.

/// Borrow the `&str` inside whichever string type the caller has.
pub(crate) trait JStr {
    fn jstr(&self) -> &str;
}

impl JStr for str {
    fn jstr(&self) -> &str {
        self
    }
}

impl JStr for String {
    fn jstr(&self) -> &str {
        self.as_str()
    }
}

impl JStr for std::sync::Arc<str> {
    fn jstr(&self) -> &str {
        self
    }
}

impl<T: JStr + ?Sized> JStr for &T {
    fn jstr(&self) -> &str {
        (*self).jstr()
    }
}

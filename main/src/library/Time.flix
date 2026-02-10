///
/// An effect used to access the current time of day.
///
eff Time {

    ///
    /// Returns the current hour of the day (0-23).
    ///
    def getHour(): Int32

}

pub mod Time {

    ///
    /// Handles the `Time` effect of the given function `f`.
    ///
    /// Returns a constant hour of 16.
    ///
    pub def handle(f: a -> b \ ef): a -> b \ (ef - Time) = x ->
        run {
            f(x)
        } with handler Time {
            def getHour(k) = k(16)
        }

    ///
    /// Runs the `Time` effect of the given function `f`.
    ///
    /// Returns a constant hour of 16.
    ///
    @DefaultHandler
    pub def runWithIO(f: Unit -> a \ ef): a \ (ef - Time) + IO = checked_ecast(handle(f)())

}

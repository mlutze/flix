/*
 * Copyright 2022 Stephen Tetley
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/// This doesn't work well - see Haskell the version with existential types for the
/// a working version.

namespace MonadLib {

    /// Catching the Error does not imply that any state is
    /// reset, but it does allow recovery from failure.
    ///
    /// Error type is fixed to string - this could change if/when Flix gets MPTCs.
    ///
    pub class MonadError[e: Type, m: Type -> Type] with Monad[m] {
        pub def throwError(e: e): m[a]

        pub def mapError(f: e -> e \ ef, m: m[a]): m[a] \ ef

        pub def catchError(m: m[a], hdl: e -> m[a] \ ef): m[a] \ ef
    }

}

namespace MonadLib/MonadError {

    use Applicative.point;
    use MonadLib.MonadError;

    pub def swapError(msg: e, ma: m[a]): m[a] with MonadError[e, m] =
        MonadLib/MonadError.mapError(_ -> msg, ma)

    pub def liftOption(e: e, x: Option[a]): m[a] with MonadError[e, m] = match x {
        case Some(x1) => point(x1)
        case None     => MonadLib/MonadError.throwError(e)
    }

    pub def liftResult(x: Result[a, e]): m[a] with MonadError[e, m] = match x {
        case Ok(x1)   => point(x1)
        case Err(msg) => MonadLib/MonadError.throwError(msg)
    }

}


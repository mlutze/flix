pub class MonadReader[r: Type, m: Type -> Type] {
    pub def ask(): m[r]

    pub def local(f: r -> r, x: m[a]): m[a]

    pub def reader(f: r -> a): m[a]
}

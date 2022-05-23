class Collection[elm, coll] {
    pub def contains(elm: elm, coll: coll): Bool
}

instance Collection[Char, String] {
    pub def contains(elm: Char, coll: String): Bool =
        String.contains(substr = "${elm}", coll)
}

instance Collection[a, List[a]] with Eq[a] {
    pub def contains(elm: a, coll: List[a]): Bool = List.memberOf(elm, coll)
}

instance Collection[(k, v), Map[k, v]] with Eq[v], Order[k] {
    pub def contains(elm: (k, v), coll: Map[k, v]): Bool =
        let (k, v) = elm;
        Map.get(k, coll) == Some(v)
}

//class ToString2[ef: Bool, a: Type] {
//    pub def toString(x: a): String & ef
//}
//
//instance ToString2[{Read(r), ef}, ScopedArray[a, r]] with ToString2[ef, a] {
//    pub def toString(a: ScopedArray[a, r]): String & {Read(r), ef} = {
//        def loop(i, acc) =
//            if (i < a.length) {
//                if (i == 0) loop(i + 1, "${a[i]}")
//                else loop(i + 1, "${acc}, ${a[i]}")
//            } else {
//                "[${acc}]"
//            };
//        loop(0, "")
//    }
//}


@test
def testContains01(): Bool = Collection.contains('a', "abc")

@test
def testContains02(): Bool = Collection.contains('b', "abc")

@test
def testContains03(): Bool = not Collection.contains('d', "abc")

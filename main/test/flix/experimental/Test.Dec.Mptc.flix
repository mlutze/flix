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

pub enum MyIterator[r: Region, a: Type](Unit -> Option[a] & r)

def mkIterator(next: Unit -> Option[a] & r1, r: Region[r]): MyIterator[r1 and r, a] = ???

pub class MyIterable[r: Region, elm: Type, a: Type] {
    pub def toIterator(x: a, r1: Region[r1]): MyIterator[r and r1, elm]
}

instance MyIterable[Pure, a, List[a]] {
    pub def toIterator(x: List[a], r1: Region[r1]): MyIterator[r1, a] = mkIterator(_ -> List.head(x), r1)
}

instance MyIterable[r1, a, Array[a, r1]] {
    pub def toIterator(x: Array[a, r1], r2: Region[r2]): MyIterator[r1 and r2, a] = mkIterator(_ -> Some(x[0]), r2)
}

//class ToString2[ef: Bool, a: Type] {
//    pub def toString(x: a): String & ef
//}
//
//instance ToString2[{Read(r), ef}, Array[a, r]] with ToString2[ef, a] {
//    pub def toString(a: Array[a, r]): String & {Read(r), ef} = {
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

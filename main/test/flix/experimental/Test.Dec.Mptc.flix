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

pub class MyForeach[r: Region, elm: Type, a: Type] {
    pub def foreach(f: elm -> Unit & ef, x: a): Unit & ef and r
}

instance MyForeach[Pure, a, List[a]] {
    pub def foreach(f: a -> Unit & ef, x: List[a]): Unit & ef = List.foreach(f, x)
}

instance MyForeach[r, a, Array[a, r]] {
    pub def foreach(f: a -> Unit & ef, x: Array[a, r]): Unit & ef and r = Array.foreach(f, x)
}

@test
def testContains01(): Bool = Collection.contains('a', "abc")

@test
def testContains02(): Bool = Collection.contains('b', "abc")

@test
def testContains03(): Bool = not Collection.contains('d', "abc")

// MATT I think we need to pull extra tparams into the tenv for these (e.g. r2)
//class ToString2[ef: Bool, a: Type] {
//    pub def toString(x: a): String & ef
//}
//
//instance ToString2[r1 and r2, Ref[a, r1]] with ToString2[r2, a] {
//    pub def toString(x: Ref[a, r1]): String & r1 and r2 = ToString2.toString(deref x)
//}
//
//instance ToString2[Pure, Int32] {
//    pub def toString(x: Int32): String = "hello"
//}
//
//@test
//def testToString01(): Bool = {
//    region r {
//        let i = ref 4 @ r;
//        ToString2.toString(i) == "hello"
//    }
//}

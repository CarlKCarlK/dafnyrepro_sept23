// include "max.dfy"

type IntRange = (int, int)
type NeIntRange = x: IntRange | !IsEmpty(x) witness (0,0)

function Max(a: int, b: int): int
{
  if a < b
  then b
  else a
}


function IsEmpty(r: IntRange): bool
{
  r.0 > r.1
}

function Contains(r: IntRange, i: int): bool
{
  r.0 <= i && i <= r.1
}

predicate Touch(i: NeIntRange, j: NeIntRange)
  ensures Touch(i, j) == exists i0, j0 :: Contains(i, i0) && Contains(j, j0) && -1 <= i0 - j0 <= 1
{
  assert Contains(i, i.0) && Contains(i, i.1) && Contains(j, j.0) && Contains(j, j.1);
  if i.1 < j.0 then
    assert  (-1 <= i.1 - j.0 <= 1) == (i.1+1 == j.0);
    i.1+1 == j.0
  else if j.1 < i.0 then
    assert (-1 <= j.1 - i.0 <= 1) == (j.1+1 == i.0);
    j.1+1 == i.0
  else
    var k0 := Max(i.0, j.0);
    assert Contains(i, k0) && Contains(j, k0);
    true
}

ghost function SeqToSet(sequence: seq<NeIntRange>): set<int>
  decreases |sequence|
  requires ValidSeq(sequence)
{
  if |sequence| == 0 then {}
  else if |sequence| == 1 then RangeToSet(sequence[0])
  else RangeToSet(sequence[0]) + SeqToSet(sequence[1..])
}


// *inclusive* range to set
ghost function RangeToSet(pair: IntRange): set<int>
{
  set i | pair.0 <= i <= pair.1 :: i
}


ghost predicate ValidSeq(sequence: seq<NeIntRange>) {
  (forall i :nat, j:nat | i < j < |sequence| :: sequence[i].0 < sequence[j].0)
  && (forall i:nat, j:nat | i < j < |sequence| :: !Touch(sequence[i], sequence[j]))
}

// cmk somehow having requires listed multiple times is necessary for the verifier to work
lemma SetsEqual(xs: seq<NeIntRange>, r: seq<NeIntRange>, r2: seq<NeIntRange>, specialIndex: nat, indexDel: nat)
  requires specialIndex < indexDel <= |xs|
  requires specialIndex < |r2|
  requires specialIndex < |xs| == |r|
  requires forall i :nat, j:nat| i < j < |xs| :: xs[i].0 < xs[j].0
  requires forall i:nat,j:nat :: i < j < |xs| && i != specialIndex && j != specialIndex ==> !Touch(xs[i], xs[j]) // only special might touch
  requires RangeToSet(xs[specialIndex]) + SeqToSet(xs[specialIndex+1..indexDel]) == RangeToSet(r[specialIndex])
  requires ValidSeq(r[..specialIndex+1]) && ValidSeq(r[specialIndex+1..]) // each half is valid
  requires ValidSeq(xs[..specialIndex+1]) && ValidSeq(xs[specialIndex+1..]) // each half is valid
  requires if indexDel < |r| then r[indexDel..] ==  r2[specialIndex+1..] else |r2| == specialIndex+1
  requires indexDel < |xs| ==> r[specialIndex].1+1 < r[indexDel].0
  requires r[..specialIndex+1] == r2[..specialIndex+1]
  requires xs[specialIndex := r[specialIndex]]== r
  ensures SeqToSet(xs[..specialIndex+1]) + SeqToSet(xs[specialIndex+1..]) == SeqToSet(r2)
  ensures forall i :nat, j:nat| i < j < |r2| :: r2[i].0 < r2[j].0
  ensures forall i:nat,j:nat :: i < j < |r2| ==> !Touch(r2[i], r2[j])
{
  RDoesntTouch(xs, r, r2, specialIndex, indexDel);
  var a := xs[..specialIndex];
  var b := xs[specialIndex..specialIndex+1];
  var b' := r[specialIndex..specialIndex+1];
  var c := xs[specialIndex+1..indexDel];
  var d := if indexDel < |xs| then xs[indexDel..] else [];
  assert xs[specialIndex+1..] == c+d;
  assert d == if indexDel < |xs| then r[indexDel..] else [];
  InsideOut2(xs[..specialIndex], xs[specialIndex]);
  assert xs[..specialIndex+1] == xs[..specialIndex] + [xs[specialIndex]];
  assert r2 == a + b' + d;
  InsideOut3(a,b);
  InsideOut3(c,d);
  InsideOut4(a,b',d);
  InsideOut3(a,b);
  assert SeqToSet(xs[..specialIndex+1]) == SeqToSet(a+b);
  assert SeqToSet(xs[specialIndex+1..]) == SeqToSet(c+d);
  assert SeqToSet(a+b) + SeqToSet(c+d) == SeqToSet(a + b' + d);
}

lemma RDoesntTouch(xs: seq<NeIntRange>, r: seq<NeIntRange>, r2: seq<NeIntRange>, specialIndex: nat, indexDel: nat)
  requires specialIndex < |xs| == |r|
  requires specialIndex < |r2|
  requires forall i :nat, j:nat| i < j < |xs| :: xs[i].0 < xs[j].0
  requires ValidSeq(xs[..specialIndex+1]) && ValidSeq(xs[specialIndex+1..]) // each half is valid
  requires ValidSeq(r[..specialIndex+1]) && ValidSeq(r[specialIndex+1..]) // each half is valid
  requires forall i:nat,j:nat :: i < j < |xs| && i != specialIndex && j != specialIndex ==> !Touch(xs[i], xs[j]) // only special might touch
  requires xs[specialIndex := r[specialIndex]]== r
  requires specialIndex < indexDel <= |xs|
  requires indexDel < |xs| ==> r[specialIndex].1+1 < r[indexDel].0
  requires r[..specialIndex+1] == r2[..specialIndex+1]
  requires if indexDel < |r| then r[indexDel..] ==  r2[specialIndex+1..] else |r2| == specialIndex+1
  ensures forall i:nat,j:nat :: i < j < |r2| ==> !Touch(r2[i], r2[j])
  ensures forall i :nat, j:nat| i < j < |r2| :: r2[i].0 < r2[j].0
{
}
lemma InsideOut2(a: seq<NeIntRange>, b: NeIntRange)
  requires ValidSeq(a) && ValidSeq(a + [b])
  ensures SeqToSet(a) + RangeToSet(b)== SeqToSet(a + [b])
{
  if |a | > 0
  {
    assert (a + [b])[1..] == a[1..] + [b];
    InsideOut2(a[1..], b);
  }
}

lemma InsideOut3(a: seq<NeIntRange>,c: seq<NeIntRange>)
  requires ValidSeq(a) && ValidSeq(c) && ValidSeq(a + c)
  ensures SeqToSet(a) + SeqToSet(c) == SeqToSet(a+c)
{
  if |a| > 0
  {
    assert (a + c)[1..] == a[1..] + c;
    InsideOut3(a[1..], c);
  }
  else
  {
    assert a+c == c;
  }
}

lemma InsideOut4(a: seq<NeIntRange>, b: seq<NeIntRange>, c: seq<NeIntRange>)
  requires ValidSeq(a) && ValidSeq(b) && ValidSeq(c) && ValidSeq(a + b + c) && ValidSeq(b + c)
  ensures SeqToSet(a) + SeqToSet(b) + SeqToSet(c) == SeqToSet(a + b + c)
{
  if |a | > 0
  {
    assert (a + b + c)[1..] == a[1..] + b + c;
  }
  else
  {
    InsideOut3(b,c);
    assert [] + b + c == b + c;
  }
}

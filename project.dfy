module Huffman {

    datatype Option<T> = None | Some(value: T)

    datatype HTree<Sym(==)> =
      | Leaf(sym: Sym, w: nat)
      | Node(w: nat, left: HTree<Sym>, right: HTree<Sym>)

    function Weight<Sym(==)>(t: HTree<Sym>): nat { t.w }

    ghost function Leaves<Sym>(t: HTree<Sym>): set<Sym>
      decreases t
    {
      match t
      case Leaf(s, _) => {s}
      case Node(_, l, r) => Leaves(l) + Leaves(r)
    }

    ghost predicate NonTrivialTree<Sym>(t: HTree<Sym>)
    {
      |Leaves(t)| >= 2
    }

    ghost predicate ValidTree<Sym>(t: HTree<Sym>)
      decreases t
    {
      match t
      case Leaf(_, w) =>
        w > 0
      case Node(w, l, r) =>
        w == Weight(l) + Weight(r) &&
        ValidTree(l) && ValidTree(r) &&
        Leaves(l) !! Leaves(r)
    }

    function PrefixMap<Sym(==)>(b: bool, m: map<Sym, seq<bool>>): map<Sym, seq<bool>>
    {
      map s | s in m.Keys :: s := [b] + m[s]
    }

    lemma PrefixMapKeys<Sym>(b: bool, m: map<Sym, seq<bool>>)
      ensures PrefixMap(b, m).Keys == m.Keys
    { }

    lemma PrefixMapLookup<Sym>(b: bool, m: map<Sym, seq<bool>>, s: Sym)
      requires s in m.Keys
      ensures PrefixMap(b, m)[s] == [b] + m[s]
    { }

    lemma MapUnionKeys<Sym>(m: map<Sym, seq<bool>>, n: map<Sym, seq<bool>>)
      requires m.Keys !! n.Keys
      ensures (m + n).Keys == m.Keys + n.Keys
    { }

    lemma MapUnionLookupLeft<Sym>(m: map<Sym, seq<bool>>, n: map<Sym, seq<bool>>, s: Sym)
      requires m.Keys !! n.Keys
      requires s in m.Keys
      ensures (m + n)[s] == m[s]
    { }

    lemma MapUnionLookupRight<Sym>(m: map<Sym, seq<bool>>, n: map<Sym, seq<bool>>, s: Sym)
      requires m.Keys !! n.Keys
      requires s in n.Keys
      ensures (m + n)[s] == n[s]
    { }

    function Codes<Sym(==)>(t: HTree<Sym>): map<Sym, seq<bool>>
      requires ValidTree(t)
      decreases t
    {
      match t
      case Leaf(s, _) => map[s := []]
      case Node(_, l, r) =>
        PrefixMap(false, Codes(l)) + PrefixMap(true, Codes(r))
    }

    lemma CodesKeys<Sym>(t: HTree<Sym>)
      requires ValidTree(t)
      ensures Codes(t).Keys == Leaves(t)
      decreases t
    {
      match t
      case Leaf(s, _) =>
      case Node(_, l, r) =>
        CodesKeys(l);
        CodesKeys(r);
        PrefixMapKeys(false, Codes(l));
        PrefixMapKeys(true, Codes(r));
        assert Codes(l).Keys !! Codes(r).Keys;
        assert PrefixMap(false, Codes(l)).Keys !! PrefixMap(true, Codes(r)).Keys;
        MapUnionKeys(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)));
    }

    lemma CodesNonEmpty<Sym>(t: HTree<Sym>)
      requires ValidTree(t) && NonTrivialTree(t)
      ensures forall s :: s in Leaves(t) ==> s in Codes(t).Keys
      ensures forall s :: s in Leaves(t) ==> |Codes(t)[s]| > 0
      decreases t
    {
      CodesKeys(t);
      assert forall s :: s in Leaves(t) ==> s in Codes(t).Keys;

      match t
      case Leaf(_, _) =>
        assert false;
      case Node(_, l, r) =>
        CodesKeys(l);
        CodesKeys(r);

        PrefixMapKeys(false, Codes(l));
        PrefixMapKeys(true, Codes(r));
        assert Codes(l).Keys !! Codes(r).Keys;
        assert PrefixMap(false, Codes(l)).Keys !! PrefixMap(true, Codes(r)).Keys;

        forall s | s in Leaves(t)
          ensures |Codes(t)[s]| > 0
        {
          if s in Leaves(l) {
            assert s in Codes(l).Keys;
            PrefixMapLookup(false, Codes(l), s);
            PrefixMapKeys(false, Codes(l));
            assert s in PrefixMap(false, Codes(l)).Keys;
            MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            assert Codes(t)[s] == PrefixMap(false, Codes(l))[s];
            assert Codes(t)[s] == [false] + Codes(l)[s];
            assert |Codes(t)[s]| > 0;
          } else {
            assert s in Leaves(r);
            assert s in Codes(r).Keys;
            PrefixMapLookup(true, Codes(r), s);
            PrefixMapKeys(true, Codes(r));
            assert s in PrefixMap(true, Codes(r)).Keys;
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            assert Codes(t)[s] == PrefixMap(true, Codes(r))[s];
            assert Codes(t)[s] == [true] + Codes(r)[s];
            assert |Codes(t)[s]| > 0;
          }
        }
    }

    predicate IsPrefix(a: seq<bool>, b: seq<bool>) {
      |a| <= |b| && forall i :: 0 <= i < |a| ==> a[i] == b[i]
    }

    predicate PrefixFreeMap<Sym>(m: map<Sym, seq<bool>>) {
      forall s, t | s in m.Keys && t in m.Keys && s != t ::
        !IsPrefix(m[s], m[t]) && !IsPrefix(m[t], m[s])
    }

    lemma PrefixMapPreservesPrefixFree<Sym>(b: bool, m: map<Sym, seq<bool>>)
      requires PrefixFreeMap(m)
      ensures PrefixFreeMap(PrefixMap(b, m))
    {
      forall s, t | s in PrefixMap(b, m) && t in PrefixMap(b, m) && s != t
        ensures !IsPrefix(PrefixMap(b, m)[s], PrefixMap(b, m)[t]) &&
                !IsPrefix(PrefixMap(b, m)[t], PrefixMap(b, m)[s])
      {
        var cs := PrefixMap(b, m)[s];
        var ct := PrefixMap(b, m)[t];
        assert s in m.Keys;
        assert t in m.Keys;

        PrefixMapLookup(b, m, s);
        PrefixMapLookup(b, m, t);

        if IsPrefix(cs, ct) {
          assert |cs| <= |ct|;
          assert |m[s]| <= |m[t]|;
          forall j | 0 <= j < |m[s]|
            ensures m[s][j] == m[t][j]
          {
            assert cs[j+1] == ct[j+1];
            assert cs[j+1] == m[s][j];
            assert ct[j+1] == m[t][j];
          }
          assert IsPrefix(m[s], m[t]);
          assert !IsPrefix(m[s], m[t]) && !IsPrefix(m[t], m[s]) by {
            assert s in m && t in m && s != t;
            assert PrefixFreeMap(m);
          }
          assert false;
        }

        if IsPrefix(ct, cs) {
          assert |ct| <= |cs|;
          assert |m[t]| <= |m[s]|;
          forall j | 0 <= j < |m[t]|
            ensures m[t][j] == m[s][j]
          {
            assert ct[j+1] == cs[j+1];
            assert ct[j+1] == m[t][j];
            assert cs[j+1] == m[s][j];
          }
          assert IsPrefix(m[t], m[s]);
          assert PrefixFreeMap(m);
          assert false;
        }
      }
    }

    lemma CodesPrefixFree<Sym>(t: HTree<Sym>)
      requires ValidTree(t)
      ensures PrefixFreeMap(Codes(t))
      decreases t
    {
      match t
      case Leaf(s, _) =>
      case Node(_, l, r) =>
        CodesPrefixFree(l);
        CodesPrefixFree(r);
        PrefixMapPreservesPrefixFree(false, Codes(l));
        PrefixMapPreservesPrefixFree(true, Codes(r));
        assert Codes(t) == PrefixMap(false, Codes(l)) + PrefixMap(true, Codes(r));
        CodesKeys(l); CodesKeys(r);
        PrefixMapKeys(false, Codes(l));
        PrefixMapKeys(true, Codes(r));
        assert PrefixMap(false, Codes(l)).Keys == Leaves(l);
        assert PrefixMap(true, Codes(r)).Keys == Leaves(r);
        assert Leaves(l) !! Leaves(r) by {
          match t
          case Node(_, l, r) => assert Leaves(l) !! Leaves(r);
        }
        assert PrefixMap(false, Codes(l)).Keys !! PrefixMap(true, Codes(r)).Keys;

        forall s, t' | s in Codes(t) && t' in Codes(t) && s != t'
          ensures !IsPrefix(Codes(t)[s], Codes(t)[t']) &&
                  !IsPrefix(Codes(t)[t'], Codes(t)[s])
        {

          CodesKeys(t);
          assert s in Leaves(t) && t' in Leaves(t);
          if s in Leaves(l) && t' in Leaves(l) {
            CodesKeys(l);
            PrefixMapKeys(false, Codes(l));
            assert s in Codes(l).Keys && t' in Codes(l).Keys;
            assert s in PrefixMap(false, Codes(l)).Keys && t' in PrefixMap(false, Codes(l)).Keys;
            MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
            assert Codes(t)[s] == PrefixMap(false, Codes(l))[s];
            assert Codes(t)[t'] == PrefixMap(false, Codes(l))[t'];
            assert PrefixFreeMap(PrefixMap(false, Codes(l)));
            assert !IsPrefix(PrefixMap(false, Codes(l))[s], PrefixMap(false, Codes(l))[t']);
            assert !IsPrefix(PrefixMap(false, Codes(l))[t'], PrefixMap(false, Codes(l))[s]);
          } else if s in Leaves(r) && t' in Leaves(r) {

            CodesKeys(r);
            PrefixMapKeys(true, Codes(r));
            assert s in Codes(r).Keys && t' in Codes(r).Keys;
            assert s in PrefixMap(true, Codes(r)).Keys && t' in PrefixMap(true, Codes(r)).Keys;
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
            assert Codes(t)[s] == PrefixMap(true, Codes(r))[s];
            assert Codes(t)[t'] == PrefixMap(true, Codes(r))[t'];
            assert PrefixFreeMap(PrefixMap(true, Codes(r)));
            assert !IsPrefix(PrefixMap(true, Codes(r))[s], PrefixMap(true, Codes(r))[t']);
            assert !IsPrefix(PrefixMap(true, Codes(r))[t'], PrefixMap(true, Codes(r))[s]);
          } else {

            if s in Leaves(l) {

              PrefixMapKeys(false, Codes(l));
              PrefixMapKeys(true, Codes(r));
              assert s in PrefixMap(false, Codes(l)).Keys;
              assert t' in PrefixMap(true, Codes(r)).Keys;
              MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
              MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
              var cs := Codes(t)[s];
              var ct := Codes(t)[t'];

              PrefixMapLookup(false, Codes(l), s);
              PrefixMapLookup(true, Codes(r), t');
              assert cs == [false] + Codes(l)[s];
              assert ct == [true] + Codes(r)[t'];
              assert cs[0] == false;
              assert ct[0] == true;

              if IsPrefix(cs, ct) {
                assert cs[0] == ct[0];
                assert false;
              }
              if IsPrefix(ct, cs) {
                assert ct[0] == cs[0];
                assert false;
              }
            } else {

              PrefixMapKeys(false, Codes(l));
              PrefixMapKeys(true, Codes(r));
              assert s in PrefixMap(true, Codes(r)).Keys;
              assert t' in PrefixMap(false, Codes(l)).Keys;
              MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
              MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
              var cs := Codes(t)[s];
              var ct := Codes(t)[t'];
              PrefixMapLookup(true, Codes(r), s);
              PrefixMapLookup(false, Codes(l), t');
              assert cs == [true] + Codes(r)[s];
              assert ct == [false] + Codes(l)[t'];
              assert cs[0] == true;
              assert ct[0] == false;
              if IsPrefix(cs, ct) {
                assert cs[0] == ct[0];
                assert false;
              }
              if IsPrefix(ct, cs) {
                assert ct[0] == cs[0];
                assert false;
              }
            }
          }
        }
    }

    function EncodeWithCodes<Sym(==)>(code: map<Sym, seq<bool>>, msg: seq<Sym>): seq<bool>
      requires forall s :: s in msg ==> s in code.Keys
      decreases |msg|
    {
      if |msg| == 0 then []
      else code[msg[0]] + EncodeWithCodes(code, msg[1..])
    }

    function Encode<Sym(==)>(t: HTree<Sym>, msg: seq<Sym>): seq<bool>
      requires ValidTree(t)
      requires forall s :: s in msg ==> s in Codes(t).Keys
      decreases |msg|
    {
      EncodeWithCodes(Codes(t), msg)
    }

    lemma EncodeLenLowerBound<Sym>(t: HTree<Sym>, msg: seq<Sym>)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> s in Codes(t).Keys
      ensures |Encode(t, msg)| >= |msg|
      decreases |msg|
    {
      if |msg| == 0 {
      } else {
        CodesNonEmpty(t);
        assert |Codes(t)[msg[0]]| > 0;
        EncodeLenLowerBound(t, msg[1..]);
      }
    }

    lemma SeqAssocBool<Sym>(b: bool, x: seq<bool>, y: seq<bool>)
      ensures ([b] + x) + y == [b] + (x + y)
    {
    }

    lemma DecodeOneFromNodeStep<Sym>(w: nat, l: HTree<Sym>, r: HTree<Sym>, bits: seq<bool>)
      requires ValidTree(Node(w, l, r))
      ensures DecodeOneFrom(Node(w, l, r), [false] + bits) == DecodeOneFrom(l, bits)
      ensures DecodeOneFrom(Node(w, l, r), [true] + bits) == DecodeOneFrom(r, bits)
    {
    }

    function DecodeOneFrom<Sym(==)>(node: HTree<Sym>, bits: seq<bool>): Option<(Sym, seq<bool>)>
      requires ValidTree(node)
      decreases node, |bits|
    {
      match node
      case Leaf(s, _) => Some((s, bits))
      case Node(_, l, r) =>
        if |bits| == 0 then None
        else if !bits[0] then DecodeOneFrom(l, bits[1..])
        else DecodeOneFrom(r, bits[1..])
    }

    lemma LookupSingleton<Sym, T>(k: Sym, v: T)
      ensures (map[k := v])[k] == v
    {
    }

    lemma DecodeOneFromCorrect<Sym>(t: HTree<Sym>, s: Sym, suffix: seq<bool>)
      requires ValidTree(t)
      requires s in Codes(t).Keys
      ensures DecodeOneFrom(t, Codes(t)[s] + suffix) == Some((s, suffix))
      decreases t
    {
      match t
      case Leaf(sym, _) =>
        assert Codes(t) == map[sym := []];
        assert s == sym;
        LookupSingleton<Sym, seq<bool>>(sym, []);
        assert Codes(t)[s] == [];
        assert DecodeOneFrom(t, suffix) == Some((sym, suffix));
        assert [] + suffix == suffix;
      case Node(_, l, r) =>
        CodesKeys(l); CodesKeys(r);
        PrefixMapKeys(false, Codes(l));
        PrefixMapKeys(true, Codes(r));
        if s in Leaves(l) {
          assert s in Codes(l).Keys;
          PrefixMapLookup(false, Codes(l), s);
          MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
          assert Codes(t)[s] == [false] + Codes(l)[s];
          calc {
            DecodeOneFrom(t, Codes(t)[s] + suffix);
            DecodeOneFrom(t, ([false] + Codes(l)[s]) + suffix);
            { SeqAssocBool<Sym>(false, Codes(l)[s], suffix); }
            DecodeOneFrom(t, [false] + (Codes(l)[s] + suffix));
          }
          DecodeOneFromNodeStep(Weight(l)+Weight(r), l, r, Codes(l)[s] + suffix);
          DecodeOneFromCorrect(l, s, suffix);
        } else {
          assert s in Leaves(r);
          assert s in Codes(r).Keys;
          PrefixMapLookup(true, Codes(r), s);
          MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
          assert Codes(t)[s] == [true] + Codes(r)[s];
          calc {
            DecodeOneFrom(t, Codes(t)[s] + suffix);
            DecodeOneFrom(t, ([true] + Codes(r)[s]) + suffix);
            { SeqAssocBool<Sym>(true, Codes(r)[s], suffix); }
            DecodeOneFrom(t, [true] + (Codes(r)[s] + suffix));
          }
          DecodeOneFromNodeStep(Weight(l)+Weight(r), l, r, Codes(r)[s] + suffix);
          DecodeOneFromCorrect(r, s, suffix);
        }
    }

    function DecodeOptionFuel<Sym(==)>(t: HTree<Sym>, bits: seq<bool>, fuel: nat): Option<seq<Sym>>
      requires ValidTree(t) && NonTrivialTree(t)
      decreases fuel
    {
      if |bits| == 0 then Some([])
      else if fuel == 0 then None
      else
        match DecodeOneFrom(t, bits)
        case None => None
        case Some(p) =>
          match DecodeOptionFuel(t, p.1, fuel - 1)
          case None => None
          case Some(restMsg) => Some([p.0] + restMsg)
    }

    function DecodeOption<Sym(==)>(t: HTree<Sym>, bits: seq<bool>): Option<seq<Sym>>
      requires ValidTree(t) && NonTrivialTree(t)
    {
      DecodeOptionFuel(t, bits, |bits|)
    }

    lemma RoundTripFuel<Sym>(t: HTree<Sym>, msg: seq<Sym>, fuel: nat)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> s in Codes(t).Keys
      requires fuel >= |msg|
      ensures DecodeOptionFuel(t, Encode(t, msg), fuel) == Some(msg)
      decreases |msg|
    {
      if |msg| == 0 {
      } else {
        DecodeOneFromCorrect(t, msg[0], Encode(t, msg[1..]));
        RoundTripFuel(t, msg[1..], fuel - 1);
        calc {
          DecodeOptionFuel(t, Encode(t, msg), fuel);
          DecodeOptionFuel(t, Codes(t)[msg[0]] + Encode(t, msg[1..]), fuel);
          match DecodeOneFrom(t, Codes(t)[msg[0]] + Encode(t, msg[1..])) {
            case None => None
            case Some(p) => match DecodeOptionFuel(t, p.1, fuel - 1) {
              case None => None
              case Some(restMsg) => Some([p.0] + restMsg)
            }
          };
          { assert DecodeOneFrom(t, Encode(t, msg)) == Some((msg[0], Encode(t, msg[1..]))); }
          match Some((msg[0], Encode(t, msg[1..]))) {
            case None => None
            case Some(p) => match DecodeOptionFuel(t, p.1, fuel - 1) {
              case None => None
              case Some(restMsg) => Some([p.0] + restMsg)
            }
          };
          match DecodeOptionFuel(t, Encode(t, msg[1..]), fuel - 1) {
            case None => None
            case Some(restMsg) => Some([msg[0]] + restMsg)
          };
          { assert DecodeOptionFuel(t, Encode(t, msg[1..]), fuel - 1) == Some(msg[1..]); }
          assert [msg[0]] + msg[1..] == msg;
          Some([msg[0]] + msg[1..]);
          Some(msg);
        }
      }
    }

    lemma DecodeEncodedRoundTrip<Sym>(t: HTree<Sym>, msg: seq<Sym>)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> s in Codes(t).Keys
      ensures DecodeOption(t, Encode(t, msg)) == Some(msg)
    {
      var bits := Encode(t, msg);
      EncodeLenLowerBound(t, msg);
      RoundTripFuel(t, msg, |bits|);
    }

    ghost function Alphabet<Sym>(freq: seq<(Sym, nat)>): set<Sym>
      decreases |freq|
    {
      if |freq| == 0 then {}
      else {freq[0].0} + Alphabet(freq[1..])
    }

    ghost predicate DistinctSyms<Sym>(freq: seq<(Sym, nat)>)
    {
      forall i, j :: 0 <= i < j < |freq| ==> freq[i].0 != freq[j].0
    }

    ghost predicate ValidFreq<Sym>(freq: seq<(Sym, nat)>)
    {
      |freq| >= 2 &&
      DistinctSyms(freq) &&
      forall i :: 0 <= i < |freq| ==> freq[i].1 > 0
    }

    ghost function MsgAlphabet<Sym>(msg: seq<Sym>): set<Sym>
      decreases |msg|
    {
      if |msg| == 0 then {}
      else {msg[0]} + MsgAlphabet(msg[1..])
    }

    ghost function SeqSet<Sym>(xs: seq<Sym>): set<Sym>
      decreases |xs|
    {
      if |xs| == 0 then {}
      else {xs[0]} + SeqSet(xs[1..])
    }

    ghost predicate DistinctSeq<Sym>(xs: seq<Sym>)
    {
      forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
    }

    function CountOf<Sym(==)>(msg: seq<Sym>, x: Sym): nat
      decreases |msg|
    {
      if |msg| == 0 then 0
      else (if msg[0] == x then 1 else 0) + CountOf(msg[1..], x)
    }


    lemma ElementInMsgAlphabet<Sym>(msg: seq<Sym>, s: Sym)
      requires s in msg
      ensures s in MsgAlphabet(msg)
    {
      if |msg| == 0 {
        assert false;
      } else if msg[0] == s {
      } else {
        assert s in msg[1..];
        ElementInMsgAlphabet(msg[1..], s);
      }
    }

lemma MsgAlphabetPrefix<Sym>(msg: seq<Sym>, i: nat)
  requires 0 <= i < |msg|
  ensures MsgAlphabet(msg[..i+1]) == MsgAlphabet(msg[..i]) + {msg[i]}
  decreases i
{
  if i == 0 {
    assert msg[..1] == [msg[0]];
    assert MsgAlphabet([msg[0]]) == {msg[0]};
    assert MsgAlphabet(msg[..0]) == {};
  } else {
    assert msg[..i+1] == [msg[0]] + msg[1..i+1];
    assert msg[..i] == [msg[0]] + msg[1..i];

    // Apply induction on the tail msg[1..]
    MsgAlphabetPrefix(msg[1..], i - 1);

    // Help Dafny identify the slices exactly
    assert (msg[1..])[..i] == msg[1..i+1];
    assert (msg[1..])[..i-1+1] == msg[1..i+1];
    assert (msg[1..])[..i-1] == msg[1..i];
    assert (msg[1..])[i-1] == msg[i];

    assert MsgAlphabet(msg[1..i+1]) == MsgAlphabet(msg[1..i]) + {msg[i]};

    calc {
      MsgAlphabet(msg[..i+1]);
      MsgAlphabet([msg[0]] + msg[1..i+1]);
      { assert MsgAlphabet([msg[0]] + msg[1..i+1]) == ({msg[0]}) + MsgAlphabet(msg[1..i+1]); }
      ({msg[0]}) + MsgAlphabet(msg[1..i+1]);
      { assert MsgAlphabet(msg[1..i+1]) == MsgAlphabet(msg[1..i]) + {msg[i]}; }
      ({msg[0]}) + (MsgAlphabet(msg[1..i]) + {msg[i]});
      (({msg[0]}) + MsgAlphabet(msg[1..i])) + {msg[i]};
      { assert ({msg[0]}) + MsgAlphabet(msg[1..i]) == MsgAlphabet(msg[..i]); }
      MsgAlphabet(msg[..i]) + {msg[i]};
    }
  }
}

lemma SeqSetAppend<Sym>(xs: seq<Sym>, x: Sym)
  ensures SeqSet(xs + [x]) == SeqSet(xs) + {x}
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    assert xs + [x] == [xs[0]] + (xs[1..] + [x]);
    calc {
      SeqSet(xs + [x]);
      SeqSet([xs[0]] + (xs[1..] + [x]));
      ({xs[0]}) + SeqSet(xs[1..] + [x]);
      { SeqSetAppend(xs[1..], x); }
      ({xs[0]}) + (SeqSet(xs[1..]) + {x});
      ({xs[0]} + SeqSet(xs[1..])) + {x};
      SeqSet(xs) + {x};
    }
  }
}

lemma IndexInSeqSet<Sym>(xs: seq<Sym>, i: nat)
  requires 0 <= i < |xs|
  ensures xs[i] in SeqSet(xs)
  decreases i
{
  if i == 0 {
  } else {
    IndexInSeqSet(xs[1..], i - 1);
  }
}

lemma DistinctSeqAppendFresh<Sym>(xs: seq<Sym>, x: Sym)
  requires DistinctSeq(xs)
  requires x !in SeqSet(xs)
  ensures DistinctSeq(xs + [x])
{
  forall i, j | 0 <= i < j < |xs + [x]|
    ensures (xs + [x])[i] != (xs + [x])[j]
  {
    if j < |xs| {
      assert xs[i] != xs[j];
    } else {
      assert j == |xs|;
      if i < |xs| {
        assert (xs + [x])[i] == xs[i];
        assert (xs + [x])[j] == x;
        if xs[i] == x {
          IndexInSeqSet(xs, i);
          assert xs[i] in SeqSet(xs);
          assert x in SeqSet(xs);
          assert false;
        }
      }
    }
  }
}

lemma InSeqSetImpliesExists<Sym>(xs: seq<Sym>, x: Sym)
  requires x in SeqSet(xs)
  ensures exists j :: 0 <= j < |xs| && xs[j] == x
  decreases |xs|
{
  if |xs| == 0 {
    assert false;
  } else {
    assert SeqSet(xs) == {xs[0]} + SeqSet(xs[1..]);
    if x == xs[0] {
      assert exists j :: 0 <= j < |xs| && xs[j] == x by {
        assert 0 <= 0 < |xs|;
      }
    } else {
      assert x in SeqSet(xs[1..]);
      InSeqSetImpliesExists(xs[1..], x);
      var j :| 0 <= j < |xs[1..]| && xs[1..][j] == x;
      assert xs[j+1] == x;
      assert exists k :: 0 <= k < |xs| && xs[k] == x by {
        assert 0 <= j + 1 < |xs|;
      }
    }
  }
}

lemma DistinctSeqNotInPrefix<Sym>(xs: seq<Sym>, i: nat)
  requires DistinctSeq(xs)
  requires 0 <= i < |xs|
  ensures xs[i] !in SeqSet(xs[..i])
{
  if xs[i] in SeqSet(xs[..i]) {
    InSeqSetImpliesExists(xs[..i], xs[i]);
    var j :| 0 <= j < |xs[..i]| && xs[..i][j] == xs[i];
    assert j < i;
    assert xs[..i][j] == xs[j];
    assert xs[j] == xs[i];
    assert false by {
      assert DistinctSeq(xs);
    }
  }
}

    lemma CountOfPositive<Sym>(msg: seq<Sym>, x: Sym)  // removed (==) because it's ghost
      requires x in MsgAlphabet(msg)
      ensures CountOf(msg, x) > 0
      decreases |msg|
    {
      if |msg| == 0 {
        assert false;
      } else if msg[0] == x {
        assert CountOf(msg, x) == 1 + CountOf(msg[1..], x);
      } else {
        assert x in MsgAlphabet(msg[1..]);
        CountOfPositive(msg[1..], x);
      }
    }

    lemma SeqSetSize<Sym>(xs: seq<Sym>)
      requires DistinctSeq(xs)
      ensures |SeqSet(xs)| == |xs|
      decreases |xs|
    {
      if |xs| == 0 {
      } else {
        assert DistinctSeq(xs[1..]);
        SeqSetSize(xs[1..]);
        assert xs[0] !in SeqSet(xs[1..]) by {
          if xs[0] in SeqSet(xs[1..]) {
            InSeqSetImpliesExists(xs[1..], xs[0]);
            var j :| 0 <= j < |xs[1..]| && xs[1..][j] == xs[0];
            assert xs[j+1] == xs[0];
            assert false by {
              assert DistinctSeq(xs);
            }
          }
        }
        assert SeqSet(xs) == {xs[0]} + SeqSet(xs[1..]);
        assert |SeqSet(xs)| == 1 + |SeqSet(xs[1..])|;
        assert |SeqSet(xs)| == 1 + |xs[1..]|;
        assert |xs| == 1 + |xs[1..]|;
      }
    }

lemma InSeqImpliesInSeqSet<Sym>(xs: seq<Sym>, x: Sym)
  requires x in xs
  ensures x in SeqSet(xs)
  decreases |xs|
{
  if |xs| == 0 {
    assert false;
  } else if x == xs[0] {
  } else {
    assert x in xs[1..];
    InSeqImpliesInSeqSet(xs[1..], x);
  }
}

lemma InSeqSetImpliesInSeq<Sym>(xs: seq<Sym>, x: Sym)
  requires x in SeqSet(xs)
  ensures x in xs
  decreases |xs|
{
  if |xs| == 0 {
    assert false;
  } else {
    assert SeqSet(xs) == {xs[0]} + SeqSet(xs[1..]);
    if x == xs[0] {
    } else {
      assert x in SeqSet(xs[1..]);
      InSeqSetImpliesInSeq(xs[1..], x);
      assert x in xs[1..];
      assert x in xs;
    }
  }
}

method DistinctSymbols<Sym(==)>(msg: seq<Sym>) returns (syms: seq<Sym>)
  ensures DistinctSeq(syms)
  ensures SeqSet(syms) == MsgAlphabet(msg)
{
  var acc: seq<Sym> := [];
  var i := 0;
  while i < |msg|
    invariant 0 <= i <= |msg|
    invariant DistinctSeq(acc)
    invariant SeqSet(acc) == MsgAlphabet(msg[..i])
  {
    if msg[i] in acc {
      InSeqImpliesInSeqSet(acc, msg[i]);
      assert msg[i] in SeqSet(acc);
      assert msg[i] in MsgAlphabet(msg[..i]);
      MsgAlphabetPrefix(msg, i);
      assert MsgAlphabet(msg[..i+1]) == MsgAlphabet(msg[..i]) + {msg[i]};
      assert MsgAlphabet(msg[..i]) + {msg[i]} == MsgAlphabet(msg[..i]);
      assert MsgAlphabet(msg[..i+1]) == MsgAlphabet(msg[..i]);
      i := i + 1;
    } else {
  var oldAcc := acc;
  if msg[i] in SeqSet(oldAcc) {
    InSeqSetImpliesInSeq(oldAcc, msg[i]);
    assert msg[i] in oldAcc;
    assert false;
  }
  acc := oldAcc + [msg[i]];
  DistinctSeqAppendFresh(oldAcc, msg[i]);
  SeqSetAppend(oldAcc, msg[i]);
  MsgAlphabetPrefix(msg, i);
  assert SeqSet(acc) == SeqSet(oldAcc) + {msg[i]};
  assert SeqSet(acc) == MsgAlphabet(msg[..i]) + {msg[i]};
  assert MsgAlphabet(msg[..i+1]) == MsgAlphabet(msg[..i]) + {msg[i]};
  assert SeqSet(acc) == MsgAlphabet(msg[..i+1]);
  i := i + 1;
}
  }
  assert i == |msg|;
  assert msg[..i] == msg;
  assert SeqSet(acc) == MsgAlphabet(msg[..i]);
  assert SeqSet(acc) == MsgAlphabet(msg);
  syms := acc;
}

lemma InFreqImpliesInAlphabet<Sym>(freq: seq<(Sym, nat)>, i: nat)
  requires 0 <= i < |freq|
  ensures freq[i].0 in Alphabet(freq)
  decreases |freq|
{
  if i == 0 {
    assert Alphabet(freq) == {freq[0].0} + Alphabet(freq[1..]);
  } else {
    InFreqImpliesInAlphabet(freq[1..], i - 1);
    assert freq[1..][i - 1].0 in Alphabet(freq[1..]);
    assert freq[1..][i - 1] == freq[i];
    assert freq[i].0 == freq[1..][i - 1].0;
    assert Alphabet(freq) == {freq[0].0} + Alphabet(freq[1..]);
  }
}

lemma DistinctSymsAppendFresh<Sym>(freq: seq<(Sym, nat)>, s: Sym, w: nat)
  requires DistinctSyms(freq)
  requires s !in Alphabet(freq)
  ensures DistinctSyms(freq + [(s, w)])
{
  forall i, j | 0 <= i < j < |freq + [(s, w)]|
    ensures (freq + [(s, w)])[i].0 != (freq + [(s, w)])[j].0
  {
    if j < |freq| {
      assert freq[i].0 != freq[j].0;
    } else {
      assert j == |freq|;
      if i < |freq| {
        assert (freq + [(s, w)])[i].0 == freq[i].0;
        assert (freq + [(s, w)])[j].0 == s;
        if freq[i].0 == s {
          InFreqImpliesInAlphabet(freq, i);
          assert false;
        }
      }
    }
  }
}

method BuildFreqFromMsg<Sym(==)>(msg: seq<Sym>) returns (freq: seq<(Sym, nat)>)
  requires |MsgAlphabet(msg)| >= 2
  ensures ValidFreq(freq)
  ensures Alphabet(freq) == MsgAlphabet(msg)
{
  var syms := DistinctSymbols(msg);
  freq := [];
  var i := 0;

  while i < |syms|
    invariant 0 <= i <= |syms|
    invariant |freq| == i
    invariant DistinctSeq(syms)
    invariant SeqSet(syms) == MsgAlphabet(msg)
    invariant DistinctSyms(freq)
    invariant forall k :: 0 <= k < |freq| ==> freq[k].1 > 0
    invariant Alphabet(freq) == SeqSet(syms[..i])
  {
    var s := syms[i];
    var w := CountOf(msg, s);

    IndexInSeqSet(syms, i);
    assert s in SeqSet(syms);
    assert s in MsgAlphabet(msg);
    CountOfPositive(msg, s);
    assert w > 0;

    DistinctSeqNotInPrefix(syms, i);
    assert s !in SeqSet(syms[..i]);
    assert s !in Alphabet(freq);

    var oldFreq := freq;
    freq := oldFreq + [(s, w)];

    DistinctSymsAppendFresh(oldFreq, s, w);
    AlphabetConcat(oldFreq, [(s, w)]);
    assert Alphabet([(s, w)]) == {s};
    assert Alphabet(freq) == Alphabet(oldFreq) + {s};
    SeqSetAppend(syms[..i], s);
    assert syms[..i+1] == syms[..i] + [s];
    assert Alphabet(freq) == SeqSet(syms[..i+1]);

    i := i + 1;
  }

  assert i == |syms|;
  assert syms[..i] == syms;
  assert Alphabet(freq) == SeqSet(syms[..i]);
  assert Alphabet(freq) == SeqSet(syms);
  assert Alphabet(freq) == SeqSet(syms);
  SeqSetSize(syms);
  assert |SeqSet(syms)| == |syms|;
  assert |SeqSet(syms)| == |MsgAlphabet(msg)|;
  assert |syms| >= 2;
  assert |freq| == |syms|;
  assert |freq| >= 2;
}

method BuildHuffmanFromMsg<Sym(==)>(msg: seq<Sym>) returns (t: HTree<Sym>)
  requires |MsgAlphabet(msg)| >= 2
  ensures ValidTree(t)
  ensures NonTrivialTree(t)
  ensures Leaves(t) == MsgAlphabet(msg)
{
  var freq := BuildFreqFromMsg(msg);
  t := BuildHuffman(freq);
  assert Alphabet(freq) == MsgAlphabet(msg);
}

  lemma InAlphabetImpliesExists<Sym>(freq: seq<(Sym, nat)>, s: Sym)
  requires s in Alphabet(freq)
  ensures exists i :: 0 <= i < |freq| && freq[i].0 == s
  decreases |freq|
  {
  if |freq| == 0 {
    assert false;
  } else if s == freq[0].0 {
    assert exists i :: 0 <= i < |freq| && freq[i].0 == s by {
      assert 0 < |freq| && freq[0].0 == s;
    }
  } else {
    assert s in Alphabet(freq[1..]);
    InAlphabetImpliesExists(freq[1..], s);
    var i :| 0 <= i < |freq[1..]| && freq[1..][i].0 == s;
    assert i+1 < |freq| && freq[i+1].0 == s;
  }
  }

lemma DisjointHeadTail<Sym>(freq: seq<(Sym, nat)>)
  requires DistinctSyms(freq) && |freq| > 0
  ensures {freq[0].0} !! Alphabet(freq[1..])
{
  if freq[0].0 in Alphabet(freq[1..]) {
    InAlphabetImpliesExists(freq[1..], freq[0].0);
    var j :| 0 <= j < |freq[1..]| && freq[1..][j].0 == freq[0].0;
    assert 0 < j+1 < |freq| && freq[j+1].0 == freq[0].0;
    assert false by {
      assert DistinctSyms(freq);
    }
  }
}

lemma AlphabetConcat<Sym>(a: seq<(Sym, nat)>, b: seq<(Sym, nat)>)
  ensures Alphabet(a + b) == Alphabet(a) + Alphabet(b)
  decreases |a|
{
  if |a| == 0 {
    assert a + b == b;
    assert Alphabet(a) == {};
    assert Alphabet(b) == Alphabet(b);
    assert Alphabet(a + b) == Alphabet(b);
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
    calc {
      Alphabet(a + b);
      Alphabet([a[0]] + (a[1..] + b));
      { assert Alphabet([a[0]] + (a[1..] + b)) == {a[0].0} + Alphabet(a[1..] + b); }
      ({a[0].0}) + Alphabet(a[1..] + b);
      { assert Alphabet(a[1..] + b) == Alphabet(a[1..]) + Alphabet(b); }
      ({a[0].0}) + (Alphabet(a[1..]) + Alphabet(b));
      ({a[0].0} + Alphabet(a[1..])) + Alphabet(b);
      { assert {a[0].0} + Alphabet(a[1..]) == Alphabet(a); }
      Alphabet(a) + Alphabet(b);
    }
  }
}

lemma AlphabetPrefix<Sym>(freq: seq<(Sym, nat)>, i: nat)
  requires 0 <= i < |freq|
  ensures Alphabet(freq[..i+1]) == Alphabet(freq[..i]) + {freq[i].0}
  decreases i
{
  if i == 0 {
    assert freq[..1] == [freq[0]];
    assert Alphabet([freq[0]]) == {freq[0].0};
    assert Alphabet(freq[..0]) == {};
    assert Alphabet(freq[..1]) == {freq[0].0};
    assert Alphabet(freq[..0]) + {freq[0].0} == {freq[0].0};
  } else {
    assert freq[..i+1] == freq[..i] + [freq[i]];
    AlphabetConcat(freq[..i], [freq[i]]);
    assert Alphabet(freq[..i+1]) == Alphabet(freq[..i]) + Alphabet([freq[i]]);
    assert Alphabet([freq[i]]) == {freq[i].0};
    assert Alphabet(freq[..i+1]) == Alphabet(freq[..i]) + {freq[i].0};
  }
}

ghost predicate SortedByWeight<Sym>(q: seq<HTree<Sym>>)
{
  forall i :: 0 <= i < |q| - 1 ==> Weight(q[i]) <= Weight(q[i + 1])
}

ghost function UnionLeaves<Sym>(q: seq<HTree<Sym>>): set<Sym>
  decreases |q|
{
  if |q| == 0 then {}
  else Leaves(q[0]) + UnionLeaves(q[1..])
}

ghost predicate DisjointQueue<Sym>(q: seq<HTree<Sym>>)
  decreases |q|
{
  if |q| <= 1 then true
  else Leaves(q[0]) !! UnionLeaves(q[1..]) && DisjointQueue(q[1..])
}

ghost predicate QueueInv<Sym>(q: seq<HTree<Sym>>, alphabet: set<Sym>)
{
  |q| >= 1 &&
  SortedByWeight(q) &&
  DisjointQueue(q) &&
  UnionLeaves(q) == alphabet &&
  forall i :: 0 <= i < |q| ==> ValidTree(q[i])
}

function InsertSorted<Sym(==)>(q: seq<HTree<Sym>>, t: HTree<Sym>): seq<HTree<Sym>>
  requires SortedByWeight(q)
  decreases |q|
{
  if |q| == 0 then [t]
  else if Weight(t) <= Weight(q[0]) then [t] + q
  else [q[0]] + InsertSorted(q[1..], t)
}

lemma InsertSortedLength<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
  requires SortedByWeight(q)
  ensures |InsertSorted(q, t)| == |q| + 1
{
  if |q| == 0 {
    assert InsertSorted(q, t) == [t];
  } else if Weight(t) <= Weight(q[0]) {
    assert InsertSorted(q, t) == [t] + q;
  } else {
    assert InsertSorted(q, t) == [q[0]] + InsertSorted(q[1..], t);
    InsertSortedLength(q[1..], t);
  }
}

lemma InsertSortedPreservesSorted<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
  requires SortedByWeight(q)
  ensures SortedByWeight(InsertSorted(q, t))
  decreases |q|
{
  if |q| == 0 {
  } else if Weight(t) <= Weight(q[0]) {
  } else {
    InsertSortedPreservesSorted(q[1..], t);
  }
}

lemma UnionLeavesInsertSorted<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
  requires SortedByWeight(q)
  ensures UnionLeaves(InsertSorted(q, t)) == UnionLeaves(q) + Leaves(t)
  decreases |q|
{
  if |q| == 0 {
    assert InsertSorted(q, t) == [t];
  } else if Weight(t) <= Weight(q[0]) {
    assert InsertSorted(q, t) == [t] + q;
    calc {
      UnionLeaves([t] + q);
      Leaves(t) + UnionLeaves(q);
    }
  } else {
    assert InsertSorted(q, t) == [q[0]] + InsertSorted(q[1..], t);
    calc {
      UnionLeaves(InsertSorted(q, t));
      UnionLeaves([q[0]] + InsertSorted(q[1..], t));
      Leaves(q[0]) + UnionLeaves(InsertSorted(q[1..], t));
    }
    UnionLeavesInsertSorted(q[1..], t);
    calc {
      Leaves(q[0]) + (UnionLeaves(q[1..]) + Leaves(t));
      (Leaves(q[0]) + UnionLeaves(q[1..])) + Leaves(t);
      UnionLeaves(q) + Leaves(t);
    }
  }
}

lemma DisjointQueueInsertSorted<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
  requires SortedByWeight(q)
  requires DisjointQueue(q)
  requires Leaves(t) !! UnionLeaves(q)
  ensures DisjointQueue(InsertSorted(q, t))
  decreases |q|
{
  if |q| == 0 {
  } else if Weight(t) <= Weight(q[0]) {
  } else {
    DisjointQueueInsertSorted(q[1..], t);
    UnionLeavesInsertSorted(q[1..], t);
    assert UnionLeaves(InsertSorted(q[1..], t)) == UnionLeaves(q[1..]) + Leaves(t);
    forall x | x in Leaves(q[0]) && x in Leaves(t)
      ensures false
    {
      assert x in UnionLeaves(q) by {
        assert Leaves(q[0]) <= UnionLeaves(q);
      }
      assert false by {
        assert Leaves(t) !! UnionLeaves(q);
      }
    }
  }
}

lemma InsertSortedPreservesValidity<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
  requires SortedByWeight(q)
  requires forall k :: 0 <= k < |q| ==> ValidTree(q[k])
  requires ValidTree(t)
  ensures forall k :: 0 <= k < |InsertSorted(q,t)| ==> ValidTree(InsertSorted(q,t)[k])
  decreases |q|
{
  if |q| == 0 { }
  else if Weight(t) <= Weight(q[0]) {
    forall k | 0 <= k < |[t] + q|
      ensures ValidTree(([t] + q)[k])
    {
      if k == 0 {
        assert ValidTree(t);
      } else {
        assert ValidTree(q[k-1]);
      }
    }
  } else {
    InsertSortedPreservesValidity(q[1..], t);
    forall k | 0 <= k < |[q[0]] + InsertSorted(q[1..], t)|
      ensures ValidTree(([q[0]] + InsertSorted(q[1..], t))[k])
    {
      if k == 0 {
        assert ValidTree(q[0]);
      } else {
        assert ValidTree(InsertSorted(q[1..], t)[k-1]);
      }
    }
  }
}

lemma AlphabetSize<Sym>(freq: seq<(Sym, nat)>)
  requires DistinctSyms(freq)
  ensures |Alphabet(freq)| == |freq|
{
  if |freq| == 0 {
  } else {
    DisjointHeadTail(freq);
    assert Alphabet(freq) == Alphabet([freq[0]]) + Alphabet(freq[1..]) by {
      assert freq == [freq[0]] + freq[1..];
      AlphabetConcat([freq[0]], freq[1..]);
    }
    assert Alphabet([freq[0]]) == {freq[0].0};
    AlphabetSize(freq[1..]);
    assert |Alphabet(freq[1..])| == |freq[1..]|;
    assert |Alphabet(freq)| == |{freq[0].0} + Alphabet(freq[1..])|;
    assert {freq[0].0} !! Alphabet(freq[1..]);
    assert |{freq[0].0} + Alphabet(freq[1..])| == 1 + |Alphabet(freq[1..])|;
    assert 1 + |Alphabet(freq[1..])| == 1 + |freq[1..]|;
    assert 1 + |freq[1..]| == |freq|;
  }
}

method CheckPrefixFree<Sym(==)>(t: HTree<Sym>) returns (ok: bool)
  requires ValidTree(t)
  ensures ok
{
  CodesPrefixFree(t);
  ok := true;
}

method BuildHuffman<Sym(==)>(freq: seq<(Sym, nat)>) returns (t: HTree<Sym>)
requires ValidFreq(freq)
ensures ValidTree(t)
ensures NonTrivialTree(t)
ensures Leaves(t) == Alphabet(freq)
{
var q: seq<HTree<Sym>> := [];
var i := 0;
while i < |freq|
  invariant 0 <= i <= |freq|
  invariant |q| == i
  invariant SortedByWeight(q)
  invariant DisjointQueue(q)
  invariant UnionLeaves(q) == Alphabet(freq[..i])
  invariant forall k :: 0 <= k < |q| ==> ValidTree(q[k])
{
  var s := freq[i].0;
  var w := freq[i].1;
  var leaf := Leaf(s, w);
  assert ValidTree(leaf);

  assert leaf.sym !in UnionLeaves(q) by {
    if leaf.sym in UnionLeaves(q) {
      assert leaf.sym in Alphabet(freq[..i]);
      InAlphabetImpliesExists(freq[..i], leaf.sym);
      var j :| 0 <= j < i && freq[..i][j].0 == leaf.sym;
      assert j < i && freq[j].0 == leaf.sym;
      assert false by {
        assert DistinctSyms(freq);
      }
    }
  }

  var oldq := q;
  q := InsertSorted(oldq, leaf);
  InsertSortedPreservesSorted(oldq, leaf);
  DisjointQueueInsertSorted(oldq, leaf);
  UnionLeavesInsertSorted(oldq, leaf);
  InsertSortedPreservesValidity(oldq, leaf);
  InsertSortedLength(oldq, leaf);
  assert |q| == |oldq| + 1;
  assert |oldq| == i;
  assert |q| == i + 1;
  AlphabetPrefix(freq, i);
  assert Alphabet(freq[..i+1]) == Alphabet(freq[..i]) + {freq[i].0};
  i := i + 1;
}

assert i == |freq|;
assert freq[..i] == freq;
assert UnionLeaves(q) == Alphabet(freq);
assert |q| >= 2;
assert QueueInv(q, Alphabet(freq));

while |q| > 1
  invariant QueueInv(q, Alphabet(freq))
  decreases |q|
{
  var oldq := q;
  var a := oldq[0];
  var b := oldq[1];
  var rest := oldq[2..];

  assert DisjointQueue([b] + rest) by {
    assert DisjointQueue(oldq) == (Leaves(a) !! UnionLeaves([b] + rest) && DisjointQueue([b] + rest));
  }
  assert Leaves(b) !! UnionLeaves(rest) by {
    assert DisjointQueue([b] + rest) ==> Leaves(b) !! UnionLeaves(rest);
  }

  var merged := Node(Weight(a) + Weight(b), a, b);
  assert ValidTree(merged);
  assert Leaves(merged) == Leaves(a) + Leaves(b);
  assert Leaves(merged) !! UnionLeaves(rest) by {
  }

  var oldrest := rest;
  q := InsertSorted(oldrest, merged);
  InsertSortedPreservesSorted(oldrest, merged);
  DisjointQueueInsertSorted(oldrest, merged);
  UnionLeavesInsertSorted(oldrest, merged);
  InsertSortedPreservesValidity(oldrest, merged);
  InsertSortedLength(oldrest, merged);
  assert |q| == |oldrest| + 1;
  assert |oldrest| == |oldq| - 2;
  assert |q| == |oldq| - 1;
}

t := q[0];
assert ValidTree(t);
assert Leaves(t) == Alphabet(freq) by {
  assert UnionLeaves(q) == Alphabet(freq);
  assert |q| == 1 ==> UnionLeaves(q) == Leaves(t);
}
AlphabetSize(freq);
assert |Leaves(t)| == |freq|;
assert |freq| >= 2;
assert |Leaves(t)| >= 2;
assert NonTrivialTree(t);
}

}
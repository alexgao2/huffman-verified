module Huffman {

    // ---------- Option type ----------
    datatype Option<T> = None | Some(value: T)

    // ---------- Huffman tree ----------
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

    // ---------- Map helpers ----------
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

    // ----- Prefix‑free property (new) -----
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

    // ---------- Encoding ----------
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

    // ---------- Decoding one symbol ----------
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

    // ---------- Decoding full stream (total via fuel) ----------
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

    // Fuel-parameterized round trip (easier to prove)
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
          // unfold definition (|bits|>0, fuel>0)
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

    // ---------- Builder inputs ----------
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

    // ---------- Helper lemmas for Alphabet ----------
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

    // ---------- Priority queue invariant (seq sorted by weight) ----------
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

    // Insert a tree into a sorted queue by weight.
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

    // ---------- BuildHuffman ----------
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

  lemma HuffmanCorrectness<Sym>(t: HTree<Sym>, msg: seq<Sym>)
    requires ValidTree(t) && NonTrivialTree(t)
    requires forall s :: s in msg ==> s in Codes(t).Keys
    ensures PrefixFreeMap(Codes(t))
    ensures DecodeOption(t, Encode(t, msg)) == Some(msg)
  {
    CodesPrefixFree(t);
    DecodeEncodedRoundTrip(t, msg);
  }


method {:test} DemoRun()
{
  var freq := [('😄', 3), ('C', 6), ('D', 4), ('A', 5), ('E', 2)];
  var t := BuildHuffman(freq);

  CodesKeys(t);

  var msg := ['😄', 'C', 'C','D','A', 'C', 'C','😄','D' ,'A','😄', 'C', 'C','D', 'E', 'A', 'A', 'E', 'D', 'A'];

  assert 'A' in Codes(t).Keys;
  assert '😄' in Codes(t).Keys;
  assert 'D' in Codes(t).Keys;

  assert forall s :: s in msg ==> s in Codes(t).Keys by {
    forall s | s in msg
      ensures s in Codes(t).Keys
    {
      assert s == 'A' || s == '😄' || s=='C'|| s == 'D' || s=='E';
    }
  }

  var bits := Encode(t, msg);
  // print "Encoded bits: ", bits, "\n";

  var decoded := DecodeOption(t, bits);
  print "Decoded: ", decoded, "\n";
}
  }
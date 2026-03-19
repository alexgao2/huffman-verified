module Huffman {

    // Core datatype for optional results.
    datatype Option<T> = None | Some(value: T)

    // Huffman tree: either a leaf with a symbol and weight, or an internal node.
    datatype HTree<Sym(==)> =
      | Leaf(sym: Sym, w: nat)
      | Node(w: nat, left: HTree<Sym>, right: HTree<Sym>)

    // Returns the stored weight of a tree node.
    function Weight<Sym(==)>(t: HTree<Sym>): nat { t.w }

    // Returns the set of symbols appearing in the leaves of the tree.
    ghost function Leaves<Sym>(t: HTree<Sym>): set<Sym>
      decreases t
    {
      match t
      case Leaf(s, _) => {s}
      case Node(_, l, r) => Leaves(l) + Leaves(r)
    }

    // A non-trivial tree has at least two distinct leaves.
    ghost predicate NonTrivialTree<Sym>(t: HTree<Sym>)
    {
      |Leaves(t)| >= 2
    }

    // ValidTree states the structural invariant for a well-formed Huffman tree.
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

    // Prefixes a bit onto every codeword in a map.
    function PrefixMap<Sym(==)>(b: bool, m: map<Sym, seq<bool>>): map<Sym, seq<bool>>
    {
      map s | s in m.Keys :: s := [b] + m[s]
    }

    // PrefixMap preserves the key set.
    lemma PrefixMapKeys<Sym>(b: bool, m: map<Sym, seq<bool>>)
      ensures PrefixMap(b, m).Keys == m.Keys
    { }

    // Lookup through PrefixMap adds the prefix bit to the stored code.
    lemma PrefixMapLookup<Sym>(b: bool, m: map<Sym, seq<bool>>, s: Sym)
      requires s in m.Keys
      ensures PrefixMap(b, m)[s] == [b] + m[s]
    { }

    // Union of disjoint maps has the union of keys.
    lemma MapUnionKeys<Sym>(m: map<Sym, seq<bool>>, n: map<Sym, seq<bool>>)
      requires m.Keys !! n.Keys
      ensures (m + n).Keys == m.Keys + n.Keys
    { }

    // Lookup on the left side of a disjoint union returns the left value.
    lemma MapUnionLookupLeft<Sym>(m: map<Sym, seq<bool>>, n: map<Sym, seq<bool>>, s: Sym)
      requires m.Keys !! n.Keys
      requires s in m.Keys
      ensures (m + n)[s] == m[s]
    { }

    // Lookup on the right side of a disjoint union returns the right value.
    lemma MapUnionLookupRight<Sym>(m: map<Sym, seq<bool>>, n: map<Sym, seq<bool>>, s: Sym)
      requires m.Keys !! n.Keys
      requires s in n.Keys
      ensures (m + n)[s] == n[s]
    { }

    // Generates the prefix-free code map induced by a valid Huffman tree.
    function Codes<Sym(==)>(t: HTree<Sym>): map<Sym, seq<bool>>
      requires ValidTree(t)
      decreases t
    {
      match t
      case Leaf(s, _) => map[s := []]
      case Node(_, l, r) =>
        PrefixMap(false, Codes(l)) + PrefixMap(true, Codes(r))
    }

    // The keys of Codes are exactly the leaves of the tree.
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

    // In a non-trivial valid tree, every symbol gets a non-empty codeword.
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
          } else {
            assert s in Leaves(r);
            assert s in Codes(r).Keys;
            PrefixMapLookup(true, Codes(r), s);
            PrefixMapKeys(true, Codes(r));
            assert s in PrefixMap(true, Codes(r)).Keys;
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            assert Codes(t)[s] == PrefixMap(true, Codes(r))[s];
            assert Codes(t)[s] == [true] + Codes(r)[s];
          }
        }
    }

    // a is a prefix of b when all bits of a match the start of b.
    predicate IsPrefix(a: seq<bool>, b: seq<bool>) {
      |a| <= |b| && forall i :: 0 <= i < |a| ==> a[i] == b[i]
    }

    // A map is prefix-free when no codeword is a prefix of another.
    predicate PrefixFreeMap<Sym>(m: map<Sym, seq<bool>>) {
      forall s, t | s in m.Keys && t in m.Keys && s != t ::
        !IsPrefix(m[s], m[t]) && !IsPrefix(m[t], m[s])
    }

    // Prefixing the same bit to all codewords preserves prefix-freeness.
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
          forall j | 0 <= j < |m[s]| ensures m[s][j] == m[t][j]
          { assert cs[j + 1] == ct[j + 1]; }
          assert IsPrefix(m[s], m[t]);
          assert false;
        }
        if IsPrefix(ct, cs) {
          forall j | 0 <= j < |m[t]| ensures m[t][j] == m[s][j]
          { assert ct[j + 1] == cs[j + 1]; }
          assert IsPrefix(m[t], m[s]);
          assert false;
        }
      }
    }

    // Codes generated from any valid Huffman tree are prefix-free.
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
        CodesKeys(l);
        CodesKeys(r);
        PrefixMapKeys(false, Codes(l));
        PrefixMapKeys(true, Codes(r));
        assert PrefixMap(false, Codes(l)).Keys == Leaves(l);
        assert PrefixMap(true, Codes(r)).Keys == Leaves(r);
        assert Leaves(l) !! Leaves(r);
        assert PrefixMap(false, Codes(l)).Keys !! PrefixMap(true, Codes(r)).Keys;

        forall s, t' | s in Codes(t) && t' in Codes(t) && s != t'
          ensures !IsPrefix(Codes(t)[s], Codes(t)[t']) &&
                  !IsPrefix(Codes(t)[t'], Codes(t)[s])
        {
          CodesKeys(t);
          if s in Leaves(l) && t' in Leaves(l) {
            CodesKeys(l);
            PrefixMapKeys(false, Codes(l));
            MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
          } else if s in Leaves(r) && t' in Leaves(r) {
            CodesKeys(r);
            PrefixMapKeys(true, Codes(r));
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
          } else if s in Leaves(l) {
            PrefixMapKeys(false, Codes(l));
            PrefixMapKeys(true, Codes(r));
            MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
            PrefixMapLookup(false, Codes(l), s);
            PrefixMapLookup(true, Codes(r), t');
            var cs := Codes(t)[s];
            var ct := Codes(t)[t'];
            assert cs[0] == false;
            assert ct[0] == true;
            if IsPrefix(cs, ct) { assert cs[0] == ct[0]; assert false; }
            if IsPrefix(ct, cs) { assert ct[0] == cs[0]; assert false; }
          } else {
            PrefixMapKeys(false, Codes(l));
            PrefixMapKeys(true, Codes(r));
            MapUnionLookupRight(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), s);
            MapUnionLookupLeft(PrefixMap(false, Codes(l)), PrefixMap(true, Codes(r)), t');
            PrefixMapLookup(true, Codes(r), s);
            PrefixMapLookup(false, Codes(l), t');
            var cs := Codes(t)[s];
            var ct := Codes(t)[t'];
            assert cs[0] == true;
            assert ct[0] == false;
            if IsPrefix(cs, ct) { assert cs[0] == ct[0]; assert false; }
            if IsPrefix(ct, cs) { assert ct[0] == cs[0]; assert false; }
          }
        }
    }

    // Encodes a message using an already-built code map.
    function EncodeWithCodes<Sym(==)>(code: map<Sym, seq<bool>>, msg: seq<Sym>): seq<bool>
      requires forall s :: s in msg ==> s in code.Keys
      decreases |msg|
    {
      if |msg| == 0 then []
      else code[msg[0]] + EncodeWithCodes(code, msg[1..])
    }

    // Encodes a message using the codes derived from the tree.
    function Encode<Sym(==)>(t: HTree<Sym>, msg: seq<Sym>): seq<bool>
      requires ValidTree(t)
      requires forall s :: s in msg ==> s in Codes(t).Keys
      decreases |msg|
    {
      EncodeWithCodes(Codes(t), msg)
    }

    // In a non-trivial tree, encoding length is at least message length.
    lemma EncodeLenLowerBound<Sym>(t: HTree<Sym>, msg: seq<Sym>)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> s in Codes(t).Keys
      ensures |Encode(t, msg)| >= |msg|
      decreases |msg|
    {
      if |msg| == 0 {
      } else {
        CodesNonEmpty(t);
        EncodeLenLowerBound(t, msg[1..]);
      }
    }

    // Boolean sequence concatenation helper.
    lemma SeqAssocBool<Sym>(b: bool, x: seq<bool>, y: seq<bool>)
      ensures ([b] + x) + y == [b] + (x + y)
    { }

    // One-step decoding from a node follows the first bit.
    lemma DecodeOneFromNodeStep<Sym>(w: nat, l: HTree<Sym>, r: HTree<Sym>, bits: seq<bool>)
      requires ValidTree(Node(w, l, r))
      ensures DecodeOneFrom(Node(w, l, r), [false] + bits) == DecodeOneFrom(l, bits)
      ensures DecodeOneFrom(Node(w, l, r), [true] + bits) == DecodeOneFrom(r, bits)
    { }

    // Decodes one symbol from the front of a bit sequence.
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

    // Lookup lemma for singleton maps.
    lemma LookupSingleton<Sym, T>(k: Sym, v: T)
      ensures (map[k := v])[k] == v
    { }

    // Decoding a symbol's own code returns that symbol and the untouched suffix.
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
        assert [] + suffix == suffix;
      case Node(_, l, r) =>
        CodesKeys(l);
        CodesKeys(r);
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
          DecodeOneFromNodeStep(Weight(l) + Weight(r), l, r, Codes(l)[s] + suffix);
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
          DecodeOneFromNodeStep(Weight(l) + Weight(r), l, r, Codes(r)[s] + suffix);
          DecodeOneFromCorrect(r, s, suffix);
        }
    }

    // Fuel-bounded decoder for full messages.
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

    // Top-level decoder uses the bit-length as fuel.
    function DecodeOption<Sym(==)>(t: HTree<Sym>, bits: seq<bool>): Option<seq<Sym>>
      requires ValidTree(t) && NonTrivialTree(t)
    {
      DecodeOptionFuel(t, bits, |bits|)
    }

    // Fuel-bounded round-trip proof.
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

    // Full encode/decode round-trip theorem.
    lemma DecodeEncodedRoundTrip<Sym>(t: HTree<Sym>, msg: seq<Sym>)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> s in Codes(t).Keys
      ensures DecodeOption(t, Encode(t, msg)) == Some(msg)
    {
      var bits := Encode(t, msg);
      EncodeLenLowerBound(t, msg);
      RoundTripFuel(t, msg, |bits|);
    }

    // Extracts the set of symbols from a frequency table.
    ghost function Alphabet<Sym>(freq: seq<(Sym, nat)>): set<Sym>
      decreases |freq|
    {
      if |freq| == 0 then {}
      else {freq[0].0} + Alphabet(freq[1..])
    }

    // Frequency entries must use distinct symbols.
    ghost predicate DistinctSyms<Sym>(freq: seq<(Sym, nat)>)
    {
      forall i, j :: 0 <= i < j < |freq| ==> freq[i].0 != freq[j].0
    }

    // A valid frequency table has at least two positive-weight symbols.
    ghost predicate ValidFreq<Sym>(freq: seq<(Sym, nat)>)
    {
      |freq| >= 2 &&
      DistinctSyms(freq) &&
      forall i :: 0 <= i < |freq| ==> freq[i].1 > 0
    }

    // Returns the set of symbols appearing in a message.
    ghost function MsgAlphabet<Sym>(msg: seq<Sym>): set<Sym>
      decreases |msg|
    {
      if |msg| == 0 then {}
      else {msg[0]} + MsgAlphabet(msg[1..])
    }

    // Converts a sequence into its underlying set of elements.
    ghost function SeqSet<Sym>(xs: seq<Sym>): set<Sym>
      decreases |xs|
    {
      if |xs| == 0 then {}
      else {xs[0]} + SeqSet(xs[1..])
    }

    // States that a sequence has no duplicates.
    ghost predicate DistinctSeq<Sym>(xs: seq<Sym>)
    {
      forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
    }

    // Counts how many times x appears in msg.
    function CountOf<Sym(==)>(msg: seq<Sym>, x: Sym): nat
      decreases |msg|
    {
      if |msg| == 0 then 0
      else (if msg[0] == x then 1 else 0) + CountOf(msg[1..], x)
    }

    // If s is in msg, then s is in MsgAlphabet(msg).
    lemma ElementInMsgAlphabet<Sym>(msg: seq<Sym>, s: Sym)
      requires s in msg
      ensures s in MsgAlphabet(msg)
    {
      if |msg| == 0 { assert false; }
      else if msg[0] == s { }
      else { ElementInMsgAlphabet(msg[1..], s); }
    }

    // Adding one more element extends the message alphabet accordingly.
    lemma MsgAlphabetPrefix<Sym>(msg: seq<Sym>, i: nat)
      requires 0 <= i < |msg|
      ensures MsgAlphabet(msg[..i + 1]) == MsgAlphabet(msg[..i]) + {msg[i]}
      decreases i
    {
      if i == 0 {
        assert msg[..1] == [msg[0]];
        assert MsgAlphabet(msg[..0]) == {};
      } else {
        MsgAlphabetPrefix(msg[1..], i - 1);
        assert (msg[1..])[..i] == msg[1..i + 1];
        assert (msg[1..])[..i - 1 + 1] == msg[1..i + 1];
        assert (msg[1..])[..i - 1] == msg[1..i];
        assert (msg[1..])[i - 1] == msg[i];
        calc {
          MsgAlphabet(msg[..i + 1]);
          { assert msg[..i + 1] == [msg[0]] + msg[1..i + 1]; }
          ({msg[0]}) + MsgAlphabet(msg[1..i + 1]);
          ({msg[0]}) + (MsgAlphabet(msg[1..i]) + {msg[i]});
          (({msg[0]}) + MsgAlphabet(msg[1..i])) + {msg[i]};
          { assert ({msg[0]}) + MsgAlphabet(msg[1..i]) == MsgAlphabet(msg[..i]); }
          MsgAlphabet(msg[..i]) + {msg[i]};
        }
      }
    }

    // Appending an element extends the set by that element.
    lemma SeqSetAppend<Sym>(xs: seq<Sym>, x: Sym)
      ensures SeqSet(xs + [x]) == SeqSet(xs) + {x}
      decreases |xs|
    {
      if |xs| == 0 { }
      else {
        assert xs + [x] == [xs[0]] + (xs[1..] + [x]);
        SeqSetAppend(xs[1..], x);
      }
    }

    // Any indexed element of a sequence belongs to its set.
    lemma IndexInSeqSet<Sym>(xs: seq<Sym>, i: nat)
      requires 0 <= i < |xs|
      ensures xs[i] in SeqSet(xs)
      decreases i
    {
      if i == 0 { } else { IndexInSeqSet(xs[1..], i - 1); }
    }

    // Appending a fresh element preserves distinctness.
    lemma DistinctSeqAppendFresh<Sym>(xs: seq<Sym>, x: Sym)
      requires DistinctSeq(xs)
      requires x !in SeqSet(xs)
      ensures DistinctSeq(xs + [x])
    {
      forall i, j | 0 <= i < j < |xs + [x]|
        ensures (xs + [x])[i] != (xs + [x])[j]
      {
        if j < |xs| {
        } else {
          assert j == |xs|;
          if i < |xs| {
            if xs[i] == x {
              IndexInSeqSet(xs, i);
              assert false;
            }
          }
        }
      }
    }

    // Membership in SeqSet implies existence of a matching index.
    lemma InSeqSetImpliesExists<Sym>(xs: seq<Sym>, x: Sym)
      requires x in SeqSet(xs)
      ensures exists j :: 0 <= j < |xs| && xs[j] == x
      decreases |xs|
    {
      if |xs| == 0 { assert false; }
      else if x == xs[0] { }
      else {
        InSeqSetImpliesExists(xs[1..], x);
        var j :| 0 <= j < |xs[1..]| && xs[1..][j] == x;
        assert xs[j + 1] == x;
      }
    }

    // In a distinct sequence, xs[i] cannot appear earlier in the prefix.
    lemma DistinctSeqNotInPrefix<Sym>(xs: seq<Sym>, i: nat)
      requires DistinctSeq(xs)
      requires 0 <= i < |xs|
      ensures xs[i] !in SeqSet(xs[..i])
    {
      if xs[i] in SeqSet(xs[..i]) {
        InSeqSetImpliesExists(xs[..i], xs[i]);
        var j :| 0 <= j < |xs[..i]| && xs[..i][j] == xs[i];
        assert j < i && xs[j] == xs[i];
        assert false;
      }
    }

    // If x belongs to the message alphabet, then its count is positive.
    lemma CountOfPositive<Sym>(msg: seq<Sym>, x: Sym)
      requires x in MsgAlphabet(msg)
      ensures CountOf(msg, x) > 0
      decreases |msg|
    {
      if |msg| == 0 { assert false; }
      else if msg[0] == x { }
      else { CountOfPositive(msg[1..], x); }
    }

    // A distinct sequence has set cardinality equal to its length.
    lemma SeqSetSize<Sym>(xs: seq<Sym>)
      requires DistinctSeq(xs)
      ensures |SeqSet(xs)| == |xs|
      decreases |xs|
    {
      if |xs| == 0 { }
      else {
        SeqSetSize(xs[1..]);
        assert xs[0] !in SeqSet(xs[1..]) by {
          if xs[0] in SeqSet(xs[1..]) {
            InSeqSetImpliesExists(xs[1..], xs[0]);
            var j :| 0 <= j < |xs[1..]| && xs[1..][j] == xs[0];
            assert xs[j + 1] == xs[0];
            assert false;
          }
        }
      }
    }

    // Sequence membership implies set membership.
    lemma InSeqImpliesInSeqSet<Sym>(xs: seq<Sym>, x: Sym)
      requires x in xs
      ensures x in SeqSet(xs)
      decreases |xs|
    {
      if |xs| == 0 { assert false; }
      else if x == xs[0] { }
      else { InSeqImpliesInSeqSet(xs[1..], x); }
    }

    // Set membership implies sequence membership.
    lemma InSeqSetImpliesInSeq<Sym>(xs: seq<Sym>, x: Sym)
      requires x in SeqSet(xs)
      ensures x in xs
      decreases |xs|
    {
      if |xs| == 0 { assert false; }
      else if x == xs[0] { }
      else { InSeqSetImpliesInSeq(xs[1..], x); }
    }

    // Computes the distinct symbols appearing in a message.
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
          MsgAlphabetPrefix(msg, i);
          i := i + 1;
        } else {
          var oldAcc := acc;
          if msg[i] in SeqSet(oldAcc) {
            InSeqSetImpliesInSeq(oldAcc, msg[i]);
            assert false;
          }
          acc := oldAcc + [msg[i]];
          DistinctSeqAppendFresh(oldAcc, msg[i]);
          SeqSetAppend(oldAcc, msg[i]);
          MsgAlphabetPrefix(msg, i);
          i := i + 1;
        }
      }
      assert msg[..i] == msg;
      syms := acc;
    }

    // Any entry in a frequency table contributes its symbol to Alphabet(freq).
    lemma InFreqImpliesInAlphabet<Sym>(freq: seq<(Sym, nat)>, i: nat)
      requires 0 <= i < |freq|
      ensures freq[i].0 in Alphabet(freq)
      decreases |freq|
    {
      if i == 0 { }
      else {
        InFreqImpliesInAlphabet(freq[1..], i - 1);
      }
    }

    // Appending a fresh symbol preserves DistinctSyms.
    lemma DistinctSymsAppendFresh<Sym>(freq: seq<(Sym, nat)>, s: Sym, w: nat)
      requires DistinctSyms(freq)
      requires s !in Alphabet(freq)
      ensures DistinctSyms(freq + [(s, w)])
    {
      forall i, j | 0 <= i < j < |freq + [(s, w)]|
        ensures (freq + [(s, w)])[i].0 != (freq + [(s, w)])[j].0
      {
        if j < |freq| { }
        else {
          if i < |freq| {
            if freq[i].0 == s {
              InFreqImpliesInAlphabet(freq, i);
              assert false;
            }
          }
        }
      }
    }

    // Builds a valid frequency table from a message with at least two symbols.
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
        assert s in MsgAlphabet(msg);
        CountOfPositive(msg, s);

        DistinctSeqNotInPrefix(syms, i);
        assert s !in Alphabet(freq);

        var oldFreq := freq;
        freq := oldFreq + [(s, w)];
        DistinctSymsAppendFresh(oldFreq, s, w);
        AlphabetConcat(oldFreq, [(s, w)]);
        assert Alphabet([(s, w)]) == {s};
        SeqSetAppend(syms[..i], s);
        assert syms[..i + 1] == syms[..i] + [s];
        i := i + 1;
      }

      assert syms[..i] == syms;
      SeqSetSize(syms);
      assert |freq| >= 2;
    }

    // Builds a Huffman tree directly from a message.
    method BuildHuffmanFromMsg<Sym(==)>(msg: seq<Sym>) returns (t: HTree<Sym>)
      requires |MsgAlphabet(msg)| >= 2
      ensures ValidTree(t)
      ensures NonTrivialTree(t)
      ensures Leaves(t) == MsgAlphabet(msg)
    {
      var freq := BuildFreqFromMsg(msg);
      t := BuildHuffman(freq);
    }

    // Membership in Alphabet(freq) implies some table entry contains that symbol.
    lemma InAlphabetImpliesExists<Sym>(freq: seq<(Sym, nat)>, s: Sym)
      requires s in Alphabet(freq)
      ensures exists i :: 0 <= i < |freq| && freq[i].0 == s
      decreases |freq|
    {
      if |freq| == 0 { assert false; }
      else if s == freq[0].0 { }
      else {
        InAlphabetImpliesExists(freq[1..], s);
        var i :| 0 <= i < |freq[1..]| && freq[1..][i].0 == s;
        assert freq[i + 1].0 == s;
      }
    }

    // The head symbol is disjoint from the alphabet of the tail.
    lemma DisjointHeadTail<Sym>(freq: seq<(Sym, nat)>)
      requires DistinctSyms(freq) && |freq| > 0
      ensures {freq[0].0} !! Alphabet(freq[1..])
    {
      if freq[0].0 in Alphabet(freq[1..]) {
        InAlphabetImpliesExists(freq[1..], freq[0].0);
        var j :| 0 <= j < |freq[1..]| && freq[1..][j].0 == freq[0].0;
        assert freq[j + 1].0 == freq[0].0;
        assert false;
      }
    }

    // Alphabet distributes over concatenation.
    lemma AlphabetConcat<Sym>(a: seq<(Sym, nat)>, b: seq<(Sym, nat)>)
      ensures Alphabet(a + b) == Alphabet(a) + Alphabet(b)
      decreases |a|
    {
      if |a| == 0 {
        assert a + b == b;
      } else {
        assert a + b == [a[0]] + (a[1..] + b);
        AlphabetConcat(a[1..], b);
      }
    }

    // Prefix extension lemma for Alphabet.
    lemma AlphabetPrefix<Sym>(freq: seq<(Sym, nat)>, i: nat)
      requires 0 <= i < |freq|
      ensures Alphabet(freq[..i + 1]) == Alphabet(freq[..i]) + {freq[i].0}
    {
      assert freq[..i + 1] == freq[..i] + [freq[i]];
      AlphabetConcat(freq[..i], [freq[i]]);
      assert Alphabet([freq[i]]) == {freq[i].0};
    }

    // Queue is sorted by nondecreasing weight.
    ghost predicate SortedByWeight<Sym>(q: seq<HTree<Sym>>)
    {
      forall i :: 0 <= i < |q| - 1 ==> Weight(q[i]) <= Weight(q[i + 1])
    }

    // Union of leaves across all trees in the queue.
    ghost function UnionLeaves<Sym>(q: seq<HTree<Sym>>): set<Sym>
      decreases |q|
    {
      if |q| == 0 then {}
      else Leaves(q[0]) + UnionLeaves(q[1..])
    }

    // Queue trees have pairwise disjoint leaf sets.
    ghost predicate DisjointQueue<Sym>(q: seq<HTree<Sym>>)
      decreases |q|
    {
      if |q| <= 1 then true
      else Leaves(q[0]) !! UnionLeaves(q[1..]) && DisjointQueue(q[1..])
    }

    // Main invariant maintained by the Huffman builder queue.
    ghost predicate QueueInv<Sym>(q: seq<HTree<Sym>>, alphabet: set<Sym>)
    {
      |q| >= 1 &&
      SortedByWeight(q) &&
      DisjointQueue(q) &&
      UnionLeaves(q) == alphabet &&
      forall i :: 0 <= i < |q| ==> ValidTree(q[i])
    }

    // Inserts a tree into a sorted queue while preserving order.
    function InsertSorted<Sym(==)>(q: seq<HTree<Sym>>, t: HTree<Sym>): seq<HTree<Sym>>
      requires SortedByWeight(q)
      decreases |q|
    {
      if |q| == 0 then [t]
      else if Weight(t) <= Weight(q[0]) then [t] + q
      else [q[0]] + InsertSorted(q[1..], t)
    }

    // InsertSorted increases queue length by one.
    lemma InsertSortedLength<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
      requires SortedByWeight(q)
      ensures |InsertSorted(q, t)| == |q| + 1
    {
      if |q| == 0 { }
      else if Weight(t) <= Weight(q[0]) { }
      else { InsertSortedLength(q[1..], t); }
    }

    // InsertSorted preserves sortedness.
    lemma InsertSortedPreservesSorted<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
      requires SortedByWeight(q)
      ensures SortedByWeight(InsertSorted(q, t))
      decreases |q|
    {
      if |q| == 0 { }
      else if Weight(t) <= Weight(q[0]) { }
      else { InsertSortedPreservesSorted(q[1..], t); }
    }

    // InsertSorted adds exactly the leaves of the inserted tree.
    lemma UnionLeavesInsertSorted<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
      requires SortedByWeight(q)
      ensures UnionLeaves(InsertSorted(q, t)) == UnionLeaves(q) + Leaves(t)
      decreases |q|
    {
      if |q| == 0 { }
      else if Weight(t) <= Weight(q[0]) { }
      else { UnionLeavesInsertSorted(q[1..], t); }
    }

    // InsertSorted preserves queue leaf disjointness.
    lemma DisjointQueueInsertSorted<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
      requires SortedByWeight(q)
      requires DisjointQueue(q)
      requires Leaves(t) !! UnionLeaves(q)
      ensures DisjointQueue(InsertSorted(q, t))
      decreases |q|
    {
      if |q| == 0 { }
      else if Weight(t) <= Weight(q[0]) { }
      else {
        DisjointQueueInsertSorted(q[1..], t);
        UnionLeavesInsertSorted(q[1..], t);
      }
    }

    // InsertSorted preserves per-element ValidTree.
    lemma InsertSortedPreservesValidity<Sym>(q: seq<HTree<Sym>>, t: HTree<Sym>)
      requires SortedByWeight(q)
      requires forall k :: 0 <= k < |q| ==> ValidTree(q[k])
      requires ValidTree(t)
      ensures forall k :: 0 <= k < |InsertSorted(q, t)| ==> ValidTree(InsertSorted(q, t)[k])
      decreases |q|
    {
      if |q| == 0 { }
      else if Weight(t) <= Weight(q[0]) { }
      else { InsertSortedPreservesValidity(q[1..], t); }
    }

    // With distinct symbols, alphabet cardinality matches table length.
    lemma AlphabetSize<Sym>(freq: seq<(Sym, nat)>)
      requires DistinctSyms(freq)
      ensures |Alphabet(freq)| == |freq|
    {
      if |freq| == 0 { }
      else {
        DisjointHeadTail(freq);
        assert freq == [freq[0]] + freq[1..];
        AlphabetConcat([freq[0]], freq[1..]);
        AlphabetSize(freq[1..]);
      }
    }

    // Executable wrapper exposing the prefix-free proof.
    method CheckPrefixFree<Sym(==)>(t: HTree<Sym>) returns (ok: bool)
      requires ValidTree(t)
      ensures ok
    {
      CodesPrefixFree(t);
      ok := true;
    }

    // Builds a valid non-trivial Huffman tree from a valid frequency table.
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

        assert leaf.sym !in UnionLeaves(q) by {
          if leaf.sym in UnionLeaves(q) {
            assert leaf.sym in Alphabet(freq[..i]);
            InAlphabetImpliesExists(freq[..i], leaf.sym);
            var j :| 0 <= j < i && freq[..i][j].0 == leaf.sym;
            assert freq[j].0 == leaf.sym;
            assert false;
          }
        }

        var oldq := q;
        q := InsertSorted(oldq, leaf);
        InsertSortedPreservesSorted(oldq, leaf);
        DisjointQueueInsertSorted(oldq, leaf);
        UnionLeavesInsertSorted(oldq, leaf);
        InsertSortedPreservesValidity(oldq, leaf);
        InsertSortedLength(oldq, leaf);
        AlphabetPrefix(freq, i);
        i := i + 1;
      }

      assert freq[..i] == freq;
      assert |q| >= 2;

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

        q := InsertSorted(rest, merged);
        InsertSortedPreservesSorted(rest, merged);
        DisjointQueueInsertSorted(rest, merged);
        UnionLeavesInsertSorted(rest, merged);
        InsertSortedPreservesValidity(rest, merged);
        InsertSortedLength(rest, merged);
      }

      t := q[0];
      assert UnionLeaves(q) == Alphabet(freq);
      assert |q| == 1 ==> UnionLeaves(q) == Leaves(t);
      AlphabetSize(freq);
    }

    // Top-level CRC wrapper.
    function CRC(msg: seq<char>): nat
    {
      CRCAcc(msg, 0)
    }

    // Running CRC-style accumulator.
    function CRCAcc(msg: seq<char>, acc: nat): nat
      decreases |msg|
    {
      if |msg| == 0 then acc
      else
        var next := ((acc * 257) + (msg[0] as nat)) % 65536;
        CRCAcc(msg[1..], next)
    }

    // Wrapped symbol type used to support single-symbol messages safely.
    datatype WSym<Sym(==)> = Real(s: Sym) | Sentinel

    // Wraps each message symbol as Real(...).
    function WrapMsg<Sym>(msg: seq<Sym>): seq<WSym<Sym>>
      decreases |msg|
    {
      if |msg| == 0 then []
      else [Real(msg[0])] + WrapMsg(msg[1..])
    }

    // Wrapping preserves message length.
    lemma WrapMsgLength<Sym>(msg: seq<Sym>)
      ensures |WrapMsg(msg)| == |msg|
      decreases |msg|
    {
      if |msg| > 0 { WrapMsgLength(msg[1..]); }
    }

    // Wrapped message index i contains Real(msg[i]).
    lemma WrapMsgIndex<Sym>(msg: seq<Sym>, i: nat)
      requires 0 <= i < |msg|
      ensures i < |WrapMsg(msg)|
      ensures WrapMsg(msg)[i] == Real(msg[i])
      decreases i
    {
      WrapMsgLength(msg);
      if i > 0 { WrapMsgIndex(msg[1..], i - 1); }
    }

    // Every element of WrapMsg is a Real symbol.
    lemma WrapMsgAllReal<Sym>(msg: seq<Sym>)
      ensures forall i :: 0 <= i < |WrapMsg(msg)| ==> WrapMsg(msg)[i].Real?
    {
      WrapMsgLength(msg);
      forall i | 0 <= i < |WrapMsg(msg)|
        ensures WrapMsg(msg)[i].Real?
      { WrapMsgIndex(msg, i); }
    }

    // Unwraps a wrapped message back to raw symbols.
    function UnwrapMsg<Sym>(wmsg: seq<WSym<Sym>>): seq<Sym>
      requires forall i :: 0 <= i < |wmsg| ==> wmsg[i].Real?
      decreases |wmsg|
    {
      if |wmsg| == 0 then []
      else [wmsg[0].s] + UnwrapMsg(wmsg[1..])
    }

    // Unwrapping preserves length when all elements are Real.
    lemma UnwrapMsgLength<Sym>(wmsg: seq<WSym<Sym>>)
      requires forall i :: 0 <= i < |wmsg| ==> wmsg[i].Real?
      ensures |UnwrapMsg(wmsg)| == |wmsg|
      decreases |wmsg|
    {
      if |wmsg| > 0 { UnwrapMsgLength(wmsg[1..]); }
    }

    // Wrapping then unwrapping returns the original message.
    lemma UnwrapWrapRoundTrip<Sym>(msg: seq<Sym>)
      ensures forall i :: 0 <= i < |WrapMsg(msg)| ==> WrapMsg(msg)[i].Real?
      ensures UnwrapMsg(WrapMsg(msg)) == msg
      decreases |msg|
    {
      WrapMsgAllReal(msg);
      if |msg| > 0 { UnwrapWrapRoundTrip(msg[1..]); }
    }

    // Simple set-cardinality helper for proving two distinct elements.
    lemma TwoDistinctInSet<T>(s: set<T>, a: T, b: T)
      requires a in s && b in s && a != b
      ensures |s| >= 2
    {
      var s' := s - {a};
      assert b in s';
      assert s == s' + {a};
      assert |s| == |s'| + 1;
      assert |s'| >= 1;
    }

    // If s occurs in msg, then Real(s) occurs in WrapMsg(msg).
    lemma RealInWrapMsg<Sym>(msg: seq<Sym>, s: Sym)
      requires s in msg
      ensures Real(s) in WrapMsg(msg)
      decreases |msg|
    {
      if msg[0] == s { }
      else { RealInWrapMsg(msg[1..], s); }
    }

    // Membership is preserved on the left of concatenation.
    lemma InConcatLeft<T>(xs: seq<T>, ys: seq<T>, x: T)
      requires x in xs
      ensures x in (xs + ys)
    {
      var i :| 0 <= i < |xs| && xs[i] == x;
      assert (xs + ys)[i] == x;
    }

    // Any element of WrapMsg(msg) is a Real symbol coming from msg.
    lemma WrapMsgElements<Sym>(msg: seq<Sym>, ws: WSym<Sym>)
      requires ws in WrapMsg(msg)
      ensures ws.Real?
      ensures ws.s in msg
      decreases |msg|
    {
      if |msg| == 0 { assert false; }
      else {
        if ws == Real(msg[0]) { }
        else {
          assert ws in WrapMsg(msg[1..]);
          WrapMsgElements(msg[1..], ws);
        }
      }
    }

    // Appending Sentinel guarantees at least two distinct wrapped symbols.
    lemma WrapMsgPlusSentinelHasTwoSymbols<Sym>(msg: seq<Sym>)
      requires |msg| > 0
      ensures |MsgAlphabet(WrapMsg(msg) + [Sentinel])| >= 2
    {
      var wrapped := WrapMsg(msg) + [Sentinel];
      WrapMsgLength(msg);
      WrapMsgIndex(msg, 0);
      assert wrapped[0] == Real(msg[0]);
      ElementInMsgAlphabet(wrapped, Real(msg[0]));
      assert wrapped[|WrapMsg(msg)|] == Sentinel;
      ElementInMsgAlphabet(wrapped, Sentinel);
      assert Real(msg[0]) != Sentinel;
      TwoDistinctInSet(MsgAlphabet(wrapped), Real(msg[0]), Sentinel);
    }

    // All real message symbols appear as leaves in the constructed wrapped tree.
    lemma AllWrappedInLeaves<Sym>(msg: seq<Sym>, t: HTree<WSym<Sym>>)
      requires |msg| > 0
      requires ValidTree(t)
      requires Leaves(t) == MsgAlphabet(WrapMsg(msg) + [Sentinel])
      ensures forall s :: s in msg ==> Real(s) in Leaves(t)
    {
      forall s | s in msg
        ensures Real(s) in Leaves(t)
      {
        RealInWrapMsg(msg, s);
        InConcatLeft(WrapMsg(msg), [Sentinel], Real(s));
        ElementInMsgAlphabet(WrapMsg(msg) + [Sentinel], Real(s));
      }
    }

    // Every wrapped symbol in WrapMsg(msg) belongs to the code map.
    lemma WrapMsgInCodes<Sym>(msg: seq<Sym>, t: HTree<WSym<Sym>>)
      requires ValidTree(t)
      requires forall s :: s in msg ==> Real(s) in Codes(t).Keys
      ensures forall ws :: ws in WrapMsg(msg) ==> ws in Codes(t).Keys
    {
      forall ws | ws in WrapMsg(msg)
        ensures ws in Codes(t).Keys
      {
        WrapMsgElements(msg, ws);
        assert ws == Real(ws.s);
      }
    }

    // Safe builder for any non-empty message, including single-symbol cases.
    method SafeBuildHuffmanFromMsg<Sym(==)>(msg: seq<Sym>) returns (t: HTree<WSym<Sym>>)
      requires |msg| > 0
      ensures ValidTree(t) && NonTrivialTree(t)
      ensures Leaves(t) == MsgAlphabet(WrapMsg(msg) + [Sentinel])
      ensures forall s :: s in msg ==> Real(s) in Codes(t).Keys
    {
      var augmented := WrapMsg(msg) + [Sentinel];
      WrapMsgPlusSentinelHasTwoSymbols(msg);
      t := BuildHuffmanFromMsg(augmented);
      AllWrappedInLeaves(msg, t);
      CodesKeys(t);
    }

    // Safe encoder for raw messages via the wrapped representation.
    method SafeEncode<Sym(==)>(t: HTree<WSym<Sym>>, msg: seq<Sym>) returns (bits: seq<bool>)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> Real(s) in Codes(t).Keys
      requires forall ws :: ws in WrapMsg(msg) ==> ws in Codes(t).Keys
      ensures bits == Encode(t, WrapMsg(msg))
    {
      bits := Encode(t, WrapMsg(msg));
    }

    // Safe decoder rejects any decoded message containing Sentinel.
    method SafeDecodeOption<Sym(==)>(t: HTree<WSym<Sym>>, bits: seq<bool>) returns (res: Option<seq<Sym>>)
      requires ValidTree(t) && NonTrivialTree(t)
    {
      var wres := DecodeOption(t, bits);
      match wres {
        case None => res := None;
        case Some(wmsg) =>
          var allReal := true;
          var i := 0;
          while i < |wmsg|
            invariant 0 <= i <= |wmsg|
            invariant allReal ==> forall j :: 0 <= j < i ==> wmsg[j].Real?
          {
            if !wmsg[i].Real? { allReal := false; }
            i := i + 1;
          }
          if allReal {
            assert forall j :: 0 <= j < |wmsg| ==> wmsg[j].Real?;
            res := Some(UnwrapMsg(wmsg));
          } else {
            res := None;
          }
      }
    }

    // Safe round-trip theorem over the wrapped layer.
    lemma SafeRoundTrip<Sym>(t: HTree<WSym<Sym>>, msg: seq<Sym>)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> Real(s) in Codes(t).Keys
      requires forall ws :: ws in WrapMsg(msg) ==> ws in Codes(t).Keys
      ensures DecodeOption(t, Encode(t, WrapMsg(msg))) == Some(WrapMsg(msg))
    {
      DecodeEncodedRoundTrip(t, WrapMsg(msg));
    }

    // Executable wrapper exposing the safe round-trip proof.
    method SafeCheckRoundTrip<Sym(==)>(t: HTree<WSym<Sym>>, msg: seq<Sym>) returns (ok: bool)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> Real(s) in Codes(t).Keys
      ensures ok
    {
      WrapMsgInCodes(msg, t);
      SafeRoundTrip(t, msg);
      ok := true;
    }

    // Safe encoding paired with a CRC checksum.
    method SafeEncodeWithCRC(t: HTree<WSym<char>>, msg: seq<char>)
      returns (bits: seq<bool>, crc: nat)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> Real(s) in Codes(t).Keys
    {
      WrapMsgInCodes(msg, t);
      bits := SafeEncode(t, msg);
      crc := CRC(msg);
    }

    // Safe decoding with checksum verification.
    method SafeDecodeWithCRC(t: HTree<WSym<char>>, bits: seq<bool>, expectedCRC: nat)
      returns (res: Option<seq<char>>)
      requires ValidTree(t) && NonTrivialTree(t)
    {
      var decoded := SafeDecodeOption(t, bits);
      if decoded.Some? {
        if CRC(decoded.value) == expectedCRC {
          res := Some(decoded.value);
        } else {
          res := None;
        }
      } else {
        res := None;
      }
    }

    // Encodes and decodes a raw message, returning the original message back.
    method SafeDecodeEncodedMessage<Sym(==)>(t: HTree<WSym<Sym>>, msg: seq<Sym>) returns (decoded: seq<Sym>)
      requires ValidTree(t) && NonTrivialTree(t)
      requires forall s :: s in msg ==> Real(s) in Codes(t).Keys
      ensures decoded == msg
    {
      WrapMsgInCodes(msg, t);
      SafeRoundTrip(t, msg);
      var wdecoded := DecodeOption(t, Encode(t, WrapMsg(msg)));
      assert wdecoded == Some(WrapMsg(msg));
      WrapMsgAllReal(msg);
      UnwrapWrapRoundTrip(msg);
      decoded := UnwrapMsg(wdecoded.value);
    }
}
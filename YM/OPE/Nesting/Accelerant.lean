import YM.OPE.Nesting.Inflate

/-! Rate of a complete term (multiplying its actual scalar child amplitudes),
with the excess log-cost rebate for positive child grades. The only place
that spends this extra exponent is a truncation of genuinely unretained terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Composite
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L:Type}{l:Filter L}{T:L→ℝ}{t:Tree}

def expense (κ:ℝ)(a:t.Inner→ℝ)(v:t.Leaf→S.Tag){n:ℕ}(q:Stage U R n t):=t.cost κ a (wages v) - (token U R t v q).1*(t.topAge κ a)

def forkBill (κ:ℝ)(a:t.Inner→ℝ)(v:t.Leaf→S.Tag)(m:ℕ):ℝ:= t.cost κ a (wages v) - m*t.topAge κ a

section Single
variable {z:Envelope L t}(v:t.Leaf→S.Tag){κ:ℝ}{a:t.Inner→ℝ}(hg:Regular l T t κ a z)
variable [l.NeBot](h:Services C F S)(hT:Tendsto T l atTop)
include hg h hT
lemma flash_rate {n:ℕ}(q:Stage U R n t) : RateLE l T (flash U R t z v q) (expense U R κ a v q) :=by
     obtain ⟨-,hd⟩:=Fusion.tariff U R hT h _ _ _ z v hg
     cases t with
     | bud=>change RateLE l T (fun _=>(1:ℂ)) (κ * ((v ()).1:ℝ) - ((v ()).1:ℝ)*κ); rw [mul_comm,sub_self]; exact RateLE.const (1:ℂ) hT
     | fork n f=> exact hd.output q.1 _
end Single
section Fork
variable {n:ℕ}{f:Fin n→Tree}{κ:ℝ}{a:(fork n f).Inner→ℝ}
variable {z:Envelope L (fork n f)}(hg:Regular l T (fork n f) κ a z)(v:(fork n f).Leaf→S.Tag)
def childExpense (a:(fork n f).Inner→ℝ){r:Fin n→ℕ}(q:Branches U R (f:=f) r)(i:Fin n):=expense U R (a (Sum.inl ())) (childAge i a) (childWages i v) (q i)
def rebate (a:(fork n f).Inner→ℝ){r:Fin n→ℕ}(q:Branches U R (f:=f) r)(i:Fin n):=(token U R (f i) (childWages i v) (q i)).1* ((f i).topAge (a (Sum.inl ())) (childAge i a)-a (Sum.inl ()))
@[simp]
lemma sum_fares {r:Fin n→ℕ}(q:Branches U R (f:=f) r)(m:ℕ):
     (∑ i:Fin n,childExpense U R v a q i)+ (weightOf (echoTags U R v q)-m)*a (Sum.inl ()) = forkBill (t:=fork n f) κ a v m - ∑ i,rebate U R v a q i :=by
     simp only [childExpense,expense,forkBill,rebate,weightOf,echoTags,degrees,weight,mul_sub,Finset.sum_sub_distrib]
     simp only [← Finset.sum_mul, sub_mul]
     change (∑ i:Fin n,(f i).cost (a (Sum.inl ())) (childAge i a) (childWages i (wages v))) - _ + _ = _
     rw [Tree.cost_fork]; change _= (∑ i,(f i).cost ..) - m * a (Sum.inl ()) - (_ - _ * a (Sum.inl ()))
     ring

lemma terms_nonnegative (h_k: ∀i,(a (Sum.inl ())) ≤ (f i).topAge (a (Sum.inl ())) (childAge i a)) {r:Fin n→ℕ}(q:Branches U R (f:=f) r)(i:Fin n):0≤rebate U R v a q i:= mul_nonneg (by positivity) (sub_nonneg.mpr (h_k i))
include hg in
lemma sum_fares_le {r:Fin n→ℕ}(q:Branches U R (f:=f) r)(m:ℕ):
     (∑ i:Fin n,childExpense U R v a q i)+ (weightOf (echoTags U R v q)-m)*a (Sum.inl ()) ≤ forkBill κ a v m :=by
     rw [sum_fares]; exact sub_le_self _ (sum_nonneg (fun i _=>terms_nonnegative U R v (fun i=>(hg.inside i).ageLower) q i))
include hg
-- note sum_fares_le uses hg; include field placement

lemma fare_omitted (D:(fork n f).Inner→ℕ)(r:Fin n→ℕ)(q:Branches U R (f:=f) r)(hD:rollCaps D ≤ r){g:ℝ}(h':gapBelow (fork n f) a D g)
     (hq:q ∈ Finset.univ \ Finset.univ.image (advance U R (f:=f) hD)): g ≤ ∑ i, rebate U R v a q i :=by
    obtain ⟨p,hp,h_d⟩:= advance_missed U R v hD hq
    exact le_trans (b:=rebate U R v a q p) (inflate.drop_cost U R (q p) (hg.inside p) (h' p) hp h_d) (Finset.single_le_sum (fun i hi=>terms_nonnegative U R v (fun i=>(hg.inside i).ageLower) q i) (Finset.mem_univ p))

variable [l.NeBot](h:Services C F S)(hT:Tendsto T l atTop)
include hT
lemma echo_room : enveloped l T (a (.inl ())) (echoPoints z) (Tree.center z) ∧ Kept l T (a (.inl ())) (echoPoints z) ∧ Tendsto (fun i=>away (echoPoints z i) (Tree.center z i)) l (𝓝 0) :=by
    let φ:Fin n→(fork n f).Positions := fun i=> (.inr ⟨i,(f i).topSeat⟩)
    refine ⟨envelope_comp (hg.extent hT) φ,fun η h=>?_, shrink_comp hg.vanish φ⟩
    exact eventually_all.mpr fun i=>eventually_all.mpr fun j=> eventually_all.mpr (fun he=>(hg.buffer i j he η h).mono fun k hx=> hx (f i).topSeat (f j).topSeat)
include h hT
lemma factor_cost {r:Fin n→ℕ}{m:ℕ}(c:R.channels m)(p:Branches U R (f:=f) r): RateLE l T (factor U R z v p c) ((weightOf (echoTags U R v p)-m)*a (Sum.inl ())):=by
    obtain ⟨he,h_b,hn⟩:=echo_room hg hT
    let x:= echoPoints z; let g:=echoTags U R v p
    let A:Atom S L := {Slot:=Fin n, tags:=g, place:=x,ft:=inferInstance, amp:=fun _=>1}; let P:Menu S L:=⟨Unit,inferInstance,fun _=>A⟩
    let M:=weightOf g*a (.inl ())
    have hp:Comparable l T z (a (.inl ())) M P:= by intro i; exact ⟨⟨_,rfl⟩,h_b,(RateLE.const _ hT).mono (by exact (sub_self M).ge)⟩
    have hh:=(Comparable.meets U R hT h hg.vanish P (hg.extent hT) hg.nonneg hp).output m c -- hn is on x, need x shrink or z?
    refine (hh.mono (show M-m*(a (.inl ()))≤_ from (sub_mul ..).ge)).congr (Eventually.of_forall fun i=>?_) -- orientation
    change ∑ _:Unit,A.issue R _ _ _ _ = _; rw [Fintype.sum_unique]; exact one_mul _

lemma one_term {r:Fin n→ℕ}{m:ℕ}(c:R.channels m)(p:Branches U R (f:=f) r): RateLE l T (fun s=>(∏ i:Fin n,flash U R (f i) (down i z) (childWages i v) (p i) s)* factor U R z v p c s) (forkBill κ a v m - ∑ i, rebate U R v a p i):=by
    have hp:=RateLE.prod (S:=Finset.univ) hT (fun i _=> flash_rate U R (Tree.childWages i v) (hg.inside i) h hT (p i))
    exact (hp.mul (factor_cost U R hg v h hT c p)).mono (sum_fares U R v p m).le
end Fork
end YM.OPE.Nesting.Composite

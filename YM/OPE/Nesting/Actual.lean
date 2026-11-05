import YM.OPE.Nesting.Clock

/-! Conversion of rate statements (initially on refinement filters) to precise
inequalities in the radii. In `Tree.toll` the non-root factors use the actual
ratios; the radius power includes **another** charged scale loss. Tested
remainders are complete discrepancies of the full kernel with its stated
finite truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory TopologicalSpace Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

namespace Tree
variable {L:Type}{n:ℕ}{f:Fin n→Tree}
-- named RHS for positive radii

def toll (w:(fork n f).Leaf→ℝ) (ε m:ℝ) (s:(fork n f).Inner→ℝ):=
   (s (.inl ()))^(m-(∑ i,w i)-ε) * ∏ p:Σ i,(f i).Inner, ((fork n f).ratios 1 s (.inr p))^(-(fork n f).headSum w (.inr p)-ε)

def bothToll (w:(fork n f).Leaf→ℝ) (ε m : ℝ)(D:(fork n f).Inner→ℕ) (s:(fork n f).Inner→ℝ) := toll w ε m s * Tree.nestPrice s D
lemma toll_eq {w:(fork n f).Leaf→ℝ}{m ε:ℝ}{s:(fork n f).Inner→ℝ}(h:0<s (.inl ())): scaleFee w s ε m= toll w ε m s:= by
    unfold scaleFee toll
    rw [prod_inner,show ratios (fork n f) 1 s (Sum.inl ())=s (Sum.inl ()) from div_one _, show (fork n f).headSum w (Sum.inl ())=∑ i,w i from rfl, Fintype.prod_sigma]
    rw [show m-(∑ i,w i)-ε=m+(- (∑ i,w i)-ε) from by ring, Real.rpow_add (x:=s (.inl ())) (by exact h)]; ring

section Positive
variable {w:(fork n f).Leaf→ℝ}{D:(fork n f).Inner→ℕ}{α:(fork n f).Inner→ℝ}
       (h : (fork n f).ordered 0 α) (h₀:(∑ i:(fork n f).Inner,α i)=1)
local notation "pays" => Tree.step

def forfeit (α:(fork n f).Inner→ℝ)(D:(fork n f).Inner→ℕ)(p:(fork n f).Inner):ℝ:= ((D p+1:ℕ):ℝ)*((fork n f).step 0 α p)
include h
lemma forfeit_nonnegative (i): 0≤forfeit α D i:= mul_nonneg (by positivity) (adequate_cost _ h i)
include h₀ in
lemma has_grain : 0<∑ v:(fork n f).Inner,(fork n f).step 0 α v:=by
    have ⟨v,hv⟩:∃ v:(fork n f).Inner,0<α v:= by
       by_contra! h'; have he:∑ v,α v≤0:=sum_nonpos fun i _=>h' i; linarith only [h₀,he]
    have hl:=step_sum_bound _ h v; rw [zero_add] at hl; exact hv.trans_le hl
omit h in
lemma penalty_all {t:Tree}{a:t.Inner→ℝ}{D':t.Inner→ℕ}{g k:ℝ}(h:∀ i:t.Inner,g ≤ ((D' i + 1:ℕ):ℝ)*(t.step k a i)): Composite.gapAll t k a D' g:=by induction t generalizing k with
    | bud=>exact True.intro
    | fork n f ih=> exact ⟨h (Sum.inl ()),fun i=>ih i (fun v=> h (Sum.inr ⟨i,v⟩))⟩
lemma penalty_below (i:Σ j:Fin n,(f j).Inner)(hf:∀v:Σ j,(f j).Inner,forfeit α D (.inr i) ≤ forfeit α D (.inr v)) : Composite.gapBelow (fork n f) α D (forfeit α D (.inr i)):=fun j=>penalty_all (fun p=> by exact hf ⟨j,p⟩)
end Positive
end Tree

section Bills
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)
variable {L:Type}{l:Filter L}[l.NeBot]{T:L→ℝ} (hT:Tendsto T l atTop)

namespace Limits
variable {n:ℕ}{f:Fin n→Tree}{z:Envelope L (fork n f)} (v:(fork n f).Leaf→S.Tag){a:(fork n f).Inner→ℝ}
       (hg:Regular l T (fork n f) (0:ℝ) a z){s:L→(fork n f).Inner→ℝ}(hs:∀t,RateIs l T (fun i=>s i t) (-a t))
       (ht:(fork n f).ordered 0 a)(h₀:∑ i:(fork n f).Inner,a i=1)
local notation "rootL" => Tree.center z

def point {t:Tree}(v:t.Leaf→S.Tag)(z:t.Envelope L)(s:L)(m:ℕ)(c:R.channels m) := R.coef m c (z s ∘ leafSeat t) (voices v) (Tree.center z s)
lemma point_eq {m:ℕ}(c:R.channels m)(s:L): (Menu.raw z v).charge R m c (Tree.center z) s=point U R v z s m c:=raw_charge _ _ _ _ _ _ s

variable {m ε γ:ℝ}(hε:0<ε){V:Type*}[Norm V]{p:L→V}
include hs ht h₀ hε hT

lemma base_charge (hp:RateLE l T p (Tree.cost (fork n f) 0 a (wages v) - m*a (.inl ()))) : ∀ᶠ i in l, ‖p i‖ ≤ Tree.toll (wages v) ε m (s i):=by
     have h':=rate_base hT hs (wages v) ε m
     have hp: RateLE l T p _:=hp
     have hP:∀ᶠ i in l, ‖p i‖ ≤Tree.scaleFee (wages v) (s i) ε m:= h'.outweigh hp (by linarith only [mul_pos hε (Tree.has_grain ht h₀)]) hT
     filter_upwards [hP, (hs (.inl ())).pos] with i h he; exact le_trans h (toll_eq he).le

lemma gain_charge (D:(fork n f).Inner→ℕ) (i:Σ v,(f v).Inner)(hp:RateLE l T p (Tree.cost (fork n f) 0 a (wages v) - m*a (.inl ())-Tree.forfeit a D (.inr i))): ∀ᶠ l' in l, ‖p l'‖ ≤ Tree.bothToll (wages v) ε m D (s l'):=by
     let γ:=forfeit a D (.inr i)
     have hv(j):=Tree.rate_ratios (a:=a) (k:=0) (by simpa using RateIs.const (c:=1) hT one_pos) hs j
     have h':=(rate_base hT hs (wages v) ε m).mul ((hv (.inr i)).power (D (.inr i)+1))
     let u(i):=Tree.scaleFee (wages v) (s i) ε m
     have hp:∀ᶠ j in l, ‖p j‖ ≤ u j*((fork n f).ratios 1 (s j) (Sum.inr i))^(D (.inr i)+1):= h'.outweigh hp (by unfold forfeit; linarith only [mul_pos hε (Tree.has_grain ht h₀)]) hT
     unfold Tree.bothToll
     filter_upwards [hp, (hs (Sum.inl ())).pos,eventually_all.mpr (fun t=>hv t|>.pos)] with j he hh ht
     rw [← Tree.toll_eq hh]; refine he.trans (mul_le_mul_of_nonneg_left (Tree.nest_price_add D ht i) ?_)
     unfold u Tree.scaleFee; exact mul_nonneg (Real.rpow_nonneg hh.le _) (prod_nonneg fun t _=> Real.rpow_nonneg (ht t).le _)

include hg h
lemma admit_output {m:ℕ}(c:R.channels m):∀ᶠ i in l, ‖point U R v z i m c‖ ≤ Tree.toll (wages v) ε m (s i) :=by
    simp_rw [← point_eq]
    exact base_charge hT v hs ht h₀ hε (Fusion.tariff U R hT h (fork n f) 0 a z v hg|>.2.output m c) -- .. holes
lemma admit_nesting {m:ℕ}(c:R.channels m)(D:(fork n f).Inner→ℕ): ∀ᶠ i in l, ‖point U R v z i m c - Composite.stacked U R m c z v D i‖ ≤ Tree.bothToll (wages v) ε m D (s i):=by
    let J:= Σ j,(f j).Inner
    rcases isEmpty_or_nonempty J with he|he
    · exact Eventually.of_forall fun i=>by
           have hh(j:Fin n): f j=Tree.bud:= by cases hf:f j with
                | bud=>exact rfl
                | fork n' f'=>exact isEmptyElim (α:=J) ⟨j, show _ from by rw [hf]; exact Sum.inl ()⟩
           rw [← point_eq,Composite.empty_gain (h:=hh),sub_self, norm_zero]; unfold Tree.bothToll nestPrice; simp only [Fintype.sum_empty,mul_zero,le_rfl]
    obtain ⟨j,hj⟩:=Finite.exists_min (fun i:J=>Tree.forfeit a D (Sum.inr i))
    simp_rw [← point_eq]; let g:=Tree.forfeit a D (.inr j)
    have hp:=Composite.echo_sized (v:=v) U R h hT g (Tree.forfeit_nonnegative ht _) c (Tree.penalty_below ht j hj) hg |>.2
    unfold Composite.echoErr Composite.forkBill at hp
    exact gain_charge hT v hs ht h₀ hε D j hp

-- full tested residue at fork

def kernel {J:Type}[Fintype J]{t:Tree}(z:t.Envelope L) (v:t.Leaf→S.Tag)(M:ℕ) (y:L→J→E4)(w:J→S.Tag)(i:L)(r:Viewers U) :ℂ:=
    formula U R (z i ∘ t.leafSeat) (Tree.center z i) (voices v) (y i) (voices w) M r

def output {J:Type}[Fintype J]{t:Tree}(z:t.Envelope L) (v:t.Leaf→S.Tag)(m:ℕ) (y:L→J→E4)(w:J→S.Tag)(i:L):U.α.unselected.algebra:=
    algebraError U R (z i ∘ t.leafSeat) (Tree.center z i) (voices v) (y i) (voices w) m

variable {J:Type}[Fintype J]{y:L→J→E4}(w:J→S.Tag)
omit h hs hg hT ht h₀ hε [l.NeBot] in
lemma kernel_formula {m:ℕ}{i:L}{r:L→Viewers U}: delta U R (Menu.raw z v) m rootL r w y i=kernel U R z v m y w i (r i):=by
    unfold delta kernel formula Orbits.trunc; rw [Menu.raw_view]
    change _ - (∑ c:Menu.Cut R m, _) = _ - _
    apply congr_arg (_-·) (?_); rw [Fintype.sum_sigma]; apply Finset.sum_congr rfl fun j _=>?_ ; refine Finset.sum_congr rfl fun c _=>?_
    change (Menu.raw z v).charge R j.val c (Tree.center z) i*_=_; rw [point_eq]; rfl

variable (hp:Intervals l T 0 z y)(hy:Kept l T 0 y)
include hp hy
omit hs ht h₀ hε
include U R v in
lemma space_kernel : ∀ᶠ i in l, Injective (beside (z i ∘ (fork n f).leafSeat) (y i)) ∧ Injective (beside (sole (rootL i)) (y i)) :=by
     have hx:= Measures.interval_comp hp ((fork n f).leafSeat) id
     have he:= Measures.interval_comp hp (fun (_:Unit)=>(fork n f).topSeat) id
     obtain ⟨b,hb,h⟩:=(Fusion.tariff U R hT h (fork n f) 0 a z v hg).1.clients
     have h₁:= (h _ le_rfl).1
     have hAge := hg.nonneg
     exact Eligible.roomAcross h₁ () hp (hy.mono (hAge.trans hb)) (hAge.trans hb) |>.and (Measures.interval_inject (Kept.sole l T rootL 0) hy he le_rfl) -- hy for h₁ needs Kept b

include hs ht h₀ hε
private lemma passes_kernel (m:ℕ)(q:L→Viewers U):∀ᶠ i in l, ‖kernel U R z v m y w i (q i)‖ ≤ Tree.toll (wages v) ε (m+1:ℝ) (s i):=by
     have he:=Measures.interval_comp hp (fun (_:Unit)=>(fork n f).topSeat) id
     have hx:=(Fusion.tariff U R hT h (fork n f) 0 a z v hg).2.tested w y m q 0 0 hy he hp le_rfl le_rfl hg.nonneg
     simp only [sub_zero,mul_zero,add_zero] at hx
     exact base_charge hT v hs ht h₀ hε (hx.congr (Eventually.of_forall fun i=> kernel_formula (r:=q) U R v w))
lemma all_kernel (m:ℕ): ∀ᶠ i in l,(∀ q:Viewers U,‖kernel U R z v m y w i q‖ ≤ Tree.toll (wages v) ε (m+1:ℝ) (s i)) ∧ ‖output U R z v m y w i‖ ≤ Tree.toll (wages v) ε (m+1:ℝ) (s i):=by
     have he:= universalize (p:=fun i q=> ‖kernel U R z v m y w i q‖ ≤ Tree.toll (wages v) ε (m+1:ℝ) (s i)) (passes_kernel U R h hT v hg hs ht h₀ hε w hp hy m)
     filter_upwards [he, space_kernel (v:=v) U R h hT hg (y:=y) hp hy] with i he hi
     exact ⟨he,glance_contract U ((norm_nonneg _).trans (he none)) |>.2 fun q=>by unfold output; rw [formula_seen _ _ _ _ _ _ _ _ _ hi.1 hi.2]; exact he q⟩
end Limits
end Bills
end YM.OPE.Nesting

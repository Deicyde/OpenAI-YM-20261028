import YM.RemainderComparison.WickReps.Hits

/-! # Preserve countable name sheets simultaneously after tilt
    Any disjoint selections; proof keeps masks and old weights. Supports for every root.
    Bound on new compact labels after assigning Transfer T x.Sciori before lift.
    Exponent and derivative costs displayed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.WickReps.Manor
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n c C f L : Side} {Y:Stars→Side} {P:BudgetPoint}{r z k w m p:ℕ}{a b β v R e x:ℝ}
variable {α:Type*}{ι J J' θ E:Type} {K : Set J}(T:Manor G c ι α J)

-- Ω support after generation.R & mark slots.Transfer Page pre-validation covers source projections
structure Quarry (S:Manor G c ι α J) (A:Set J) (E:Type) (root:ι→Support c)(r:ℕ) where
    etc : E→ RegularAddress c
    truss i : (etc i).support=neighbors r (etc i).site
    panel : E→Finset J
    sign : E→ Multiset ι
    wards : ∀ i j,j∈sign i→ root j ⊆ (etc i).support -- j implicit error
    meets i j: j∈panel i→j∈A ∧ S.halls j⊆(etc i).support∧ S.marks j=sign i
    once i j : i≠j→Disjoint (panel i) (panel j)

variable {root:ι→Support c} (Q:Quarry T K E root r)(P:BudgetPoint)
set_option quotPrecheck false
local notation "o"=> fun i=> (Q.etc i).site
local notation "M"=> Q.panel
variable (H:2*w≤f.val)(g:α→E→ Config G f→ℝ) (b:E→ℝ)
def stave (u:α) (i:E) : Config G c→ℝ:= ∑ j∈Q.panel i,T.solvent u j
def compass (u:α)(i:E) (V: Config G c):= ∑ j∈Q.panel i,T.wet P u j V

def vessel (k:ℕ) : Manor G c ι α E := ⟨fun i=>⟨o i,neighbors k (o i),(neighbors_mem ..).2 (by rw [separation_self]; omega)⟩,fun u i=>b i • ((g u i)∘garment H (o i) r),Q.sign, fun _=> False ⟩
local notation "X" => vessel T Q H g b k
def zephyr (k:ℕ) (u:α)(i:E) (V:Config G c):= compass T Q P u i V - (vessel T Q H g b k).wet P u i V
local notation "Y'" => zephyr T Q P H g b k
variable {σ V β':ℝ}
local notation "fee" => burse P k z a

def tribute (m r:ℕ) (a x:ℝ):= Real.exp (a*((m+m+1)^4:ℕ))* ((ballCost r)*x)
variable (hh:2*r≤w) (hw:w+1≤ z)(hv:2*z≤ k)(hf:2*z<c.val)(hX: Arc.Deduct G P β z R)
variable (hb:∀ i,0≤ b i) (hp:∀ u i,P.Regular univ (g u i)) (hρ:∀ i u,Mare P (g u i) β R a) (ha:0≤a) (hx:∀ x:Site c,SumBudget (fun i=> if (Q.etc i).site=x then b i else 0) β')
variable (hk:k ≤ m*P.B)(hs:0≤ σ)
include hh hw hv hf hX hb hp hρ ha
lemma bless (u:α)(i:E) : Sees X P root i ∧ ∀ x ∈ neighbors k (o i), P.supBounds x (neighbors k (o i)) ((X).solvent u i) (fee*b i) :=by
    have he:=opal (g u i) H hh (o i) hw hf hv hX (hp u i) ha (hρ i u); have hg : P.Regular (neighbors k (o i)) ((X).solvent u i):= CouplingShape.reg_scale _ he.1
    refine ⟨⟨fun a=> ?_,?_,fun a hv=> by contradiction⟩,fun x hx=>?_⟩
    · exact CouplingShape.reg_scale _ ((opal (g a i) H hh (o i) hw hf hv hX (hp a i) ha (hρ i a)).1)
    · intro a j hj V h; have hp:= Q.wards i j hj; rw [Q.truss] at hp; exact hp.trans (Corona.halo_mono (show r≤ k by omega) Subset.rfl)
    rw [mul_comm]; have h:=CouplingShape.sup_scale (b i) (he.2 x hx); rw [abs_of_nonneg (hb i)] at h; exact h
include hk hx hs
variable [Nonempty α]
lemma factor : Spinal X Set.univ root P σ (fee * tribute m k σ β'):=by
    have hm: Ac.Hit (X).halls P.B b σ (tribute m k σ β'):= boot P hk hb hx σ hs
    have he:0≤ burse P k z a:=by unfold burse Trio.tilt; positivity
    refine ⟨fun i=>fee*b i,fun i=> mul_nonneg he (hb _),fun i _=>?_,hit_scale he hm⟩
    exact ⟨(bless T Q P H g b hh hw hv hf hX hb hp hρ ha Classical.ofNonempty i).1,fun a=> (bless T Q P H g b hh hw hv hf hX hb hp hρ ha a i).2⟩
variable (u:α)(h:T.Templary K root P V v)(hW:0≤ V)(hC:4*r+16≤c.val)(hS:∀ u i, Matches (T.stave Q u i) (g u i) P r ((Q.etc i).site) (b i))
include h hW hC hS
-- hit sums of omitted mismasks. Global marks retained.
structure Nimble (T:Manor G c ι α J)(Q:Quarry T K E root r)(P:BudgetPoint)(HJ:Manor G c ι α E) (f:α→ E→ Config G c→ℝ) (a b:ℝ) : Prop where
    letters i a : Flues.apex root ((HJ).halls i) (Q.sign i) (f a i)
    awake i a : Trio.Tidy P ((HJ).halls i) (f a i)
    missed i a U : Healthy P.threshold ((HJ).halls i) U→ f a i U=0
    budget : ∃ g:E→ℝ,(∀ i,0≤g i)∧ Ac.Hit HJ.halls P.B g a b∧ ∀ i a U, ‖f a i U‖ ≤ g i

omit [Nonempty α] hS hh hw hv hf hX hk hx hp hρ ha hb hs hC in
lemma counted : ∃ f:E→ℝ,(∀ i,0≤ f i) ∧ (∀ x:Site c, SumBudget (fun i=> if (Q.etc i).site=x then f i else 0) ((ballCost r)*v))∧ ∀ i u V, ‖T.compass Q P u i V‖≤ f i:=by
    obtain ⟨g,hf,hp,hh⟩:=h.grants
    let f i:=∑ j∈Q.panel i,g j; have ht i:0 ≤ f i:= sum_nonneg fun i _=> hf i
    refine ⟨f,ht,fun x=>budget_of_sum (fun i=>by split; exact ht _; exact le_rfl) (fun i=> ?_),fun i u x=>?_⟩
    · let v i j:= if T.port i=j then g i*Real.exp (V*coverNumber P.B (T.halls i)) else 0
      let t:= i.filter (fun i=> o i=x); let q:= t.biUnion (fun i=>Q.panel i)
      let HJ:= neighbors r x; have hk (i)(hx:i∈q): T.port i∈ HJ :=by
          obtain ⟨i,h,hv'⟩:= mem_biUnion.mp hx; apply ((Q.truss i).trans (congr_arg (neighbors r) ((mem_filter.mp h).2))) ▸ (Q.meets i _ hv').2.1 (T.call _)
      have hg: ∑ j∈i,(if (Q.etc j).site=x then f j else 0)=∑ j∈q,g j:=by rw [← sum_filter]; exact (sum_biUnion (show (t:Set E).PairwiseDisjoint Q.panel from fun _ _ _ _ h=> Q.once _ _ h)).symm
      rw [hg]; refine (sum_le_sum (fun j hj=> (?_ : g j ≤ ∑ y∈HJ,v j y))).trans ?_
      swap; · rw [sum_comm]; apply le_trans (sum_le_sum (fun j _=> budget_sum (hh j) q)); rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) (budget_nonneg (hh x))
      unfold v; rw [sum_ite_eq,if_pos (hk _ hj)]; exact le_mul_of_one_le_right (hf j) (Real.one_le_exp (mul_nonneg hW (by positivity)))
    exact (norm_sum_le ..).trans (sum_le_sum (fun j hj=>wet_le u x (hp _ (Q.meets i j hj).1|>.1) ((hp _ (Q.meets i j hj).1).2 u)))
lemma winds : Nimble T Q P X (zephyr T Q P H g b k) σ (fee * tribute m k σ β'+ tribute m k σ ((ballCost r)*v)) :=by
    have he:=(factor T Q P H g b hh hw hv hf hX hb hp hρ ha hx hk hs).templary; have hg : r≤ k:=by omega
    refine ⟨?_,?_,?_,?_⟩
    · intro i u j hj U ht; have hp:= Q.wards i j hj; rw [Q.truss] at hp; exact hp.trans (Corona.halo_mono hg Subset.rfl)
    · intro i a; apply Trio.tidy_sub P (u:= fun V=> compass T Q P a i V) (v:= (X).wet P a i) _ ((X).tidied a ((he.grants.choose_spec.2.1 i (Set.mem_univ i)).1) Subset.rfl); refine Trio.tidy_sum P ((X).halls i) _ _ fun j hj=>?_
      obtain ⟨hj,hF,hx⟩:= Q.meets i j hj; rw [Q.truss] at hF; exact T.tidied _ (h.grants.choose_spec.2.1 j hj|>.1) (hF.trans (Corona.halo_mono hg Subset.rfl))
    · intro i a V hV; unfold zephyr; apply sub_eq_zero.mpr; rw [onView _ _ hV]; change compass _ _ _ _ _ _= _*_; rw [Function.comp_apply,← refined (g a i) H hh (o i) hw hv V hC (hS a i) hV]; unfold stave compass; rw [Finset.sum_apply]; refine sum_congr rfl (fun j hj=>?_); have he:=(Q.meets i j hj).2.1; rw [Q.truss] at he; exact onView _ _ (hV.mono_left (he.trans (Corona.halo_mono hg Subset.rfl)))
    obtain ⟨f,hf',hz,h⟩:= counted T Q P h hW
    obtain ⟨gF,hg,hc,hT⟩:=(factor T Q P H g b hh hw hv hf hX hb hp hρ ha hx hk hs).grants
    refine ⟨fun i=>gF i+f i,fun i=> add_nonneg (hg _) (hf' _), RecursiveSecants079.BothSides.hit_plus hT (boot P hk hf' hz σ hs),fun i a V=>?_⟩
    dsimp only; unfold zephyr; rw [add_comm]; apply (norm_sub_le ..).trans; exact add_le_add (h ..) (wet_le a V (hc i (Set.mem_univ i)|>.1) ((hc i (Set.mem_univ i)).2 a _ ((X).call i))) -- name g shadow
end YM.RemainderComparison.WickReps.Manor

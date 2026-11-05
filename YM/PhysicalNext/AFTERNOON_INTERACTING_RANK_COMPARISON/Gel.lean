import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Orders
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Accumulator
import YM.Further.FREE_COVARIANCE_KP.KP.Gem
import YM.Next.RANK.Prepaid
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Folios
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.TiltField
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Arc.Audit
import YM.Push.ABSOLUTE_SUMS.Breadth
import YM.Push.GRID_APPROXIMATION.Roll

/-!
# Compatibility with *all* authorized source-K choices in Choir

Grouping in strictly the same footprint (including all positions) and
inventory so supports of different images don't lose flags or incompatibility.
No transformations on Hard U. Zero-marker slots of every authorized choice
read exactly the canonical K. Internal eligibility & zero conditions still
constrain these values (no substituting different values on them).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Gel
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Glyph Marker
open scoped Topology BigOperators Classical
variable {V ι κ : Type} [Fintype V] [DecidableEq V] [Fintype ι] {G : Gauge} {n : Side} {θ : V→ Site n} {P : Rep G n} {τ : ℝ}

/-- compat data at the input. -/
def calls (s : Lifted G θ τ) : addressKey n := ⟨(s.extent,s.inventory),s.needed,s.records⟩
abbrev Setting (θ : V→ Site n) := { i : addressKey n × modes V // ∀ t∈i.2.val,θ t ∈ i.1.val.1 }
def name (s : Lifted G θ τ) : Setting θ := ⟨(calls s,s.fires),s.remembers⟩

variable (K : ι → Lifted G θ τ)
abbrev Riders (i : Setting θ) := { t : ι // name (K t) = i }

-- skin remembers every original K partner at the given address/mode.
-- extensions Gauge-invariant on Rank syntax.
def freezeKey (i : Setting θ) : Lifted G θ τ where
  extent:= i.val.1.val.1
  inventory:= i.val.1.val.2
  needed:=i.val.1.property.1
  records:=i.val.1.property.2
  fires:=i.val.2
  remembers:=i.property
  value U:=∑ j:Riders K i,(K j).value U
  meas:= Finset.measurable_fun_sum _ fun i _=> (K i.val).meas
  flag U := by
    intro he; obtain ⟨j,-,hj⟩:= Finset.exists_ne_zero_of_sum_ne_zero he
    rw [← j.property]; exact (K j).flag _ hj
  only:= by
    intro U V hp hf; apply sum_congr rfl; intro x _
    have he := x.property; rw [← he] at hp hf
    exact (K x).only _ _ hp hf
  inv:= fun t V=> Finset.sum_congr rfl fun i _=> (K i).inv ..
lemma earned (p : BudgetPoint) (K : ι → Lifted G θ p.threshold) (r : V → ℝ) {e L} (hr : ∀ i,0<r i) (hp : Stripes p K r e L) : Stripes p (freezeKey K) r e L := by
  obtain ⟨c,h,H⟩ := hp
  let c' (i : Setting θ) := ∑ j:Riders K i,c j
  refine ⟨c',fun i=> ⟨Finset.sum_nonneg fun j _=>(h j.val).1,fun U=>?_⟩,fun x=>?_⟩
  · let a:=charge p e i.val.1.val.1 ; let b:= Poly.toll r i.val.2
    apply (mul_le_mul_of_nonneg_left (norm_sum_le Finset.univ _) (show 0≤ a*b from mul_nonneg (Real.exp_pos _).le (Poly.worth hr _).le)).trans
    rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_
    have ht:= (h j.val).2 U
    have hx : (K j.val).extent=i.val.1.val.1:= congr_arg (fun (t:Setting θ)=>t.val.1.val.1) j.property
    have hy : (K j.val).fires=i.val.2:= congr_arg (fun (t:Setting θ)=>t.val.2) j.property
    rw [hx,hy] at ht; exact ht
  refine le_trans (le_of_eq ?_) (H x)
  rw [← Fintype.sum_fiberwise (fun t=> name (K t)) (fun i=> if x ∈ (K i).extent then c i else 0)]
  apply Finset.sum_congr rfl; intro i _; change (if x∈i.val.1.val.1 then c' i else 0) = _
  split
  next he => exact Finset.sum_congr rfl fun j _=> (if_pos (show x∈(K j).extent from (show x∈ i.val.1.val.1 from he) |> fun he=> by rw [← j.property] at he; exact he)).symm
  next he => symm
             exact Finset.sum_eq_zero fun j _=>if_neg (fun hv=>he (by rw [← j.property]; exact hv))

def hush (θ : V→ Site n) (i : addressKey n) : Setting θ := ⟨(i,quiet V),fun _ h=>False.elim (notMem_empty _ h)⟩

def archived {σ C Λ δ w : ℝ} (Q : Rep G n) (θ : V→ Site n) (h : Q.Lawful σ C Λ δ w) (i : addressKey n) : Lifted G θ Q.p.threshold where
  extent:= i.val.1
  inventory:= i.val.2
  needed:= i.property.1
  records:= i.property.2
  fires:=Glyph.quiet V
  remembers:= (hush θ i).property
  value U:= (↑(Value.Archive Q.activities i U) : ℂ)
  meas:= by
    apply Complex.continuous_ofReal.measurable.comp
    unfold Value.Archive; refine Measurable.tsum ?_; intro i; split <;> first |exact h.labels.forced.meas _|exact measurable_const
  flag U hv:= by
    let A:=Q.activities; by_contra hU
    have he : Value.Archive Q.activities i U=0:= by
      apply Eq.trans _ (tsum_zero (L:=SummationFilter.unconditional ℕ) (α:=ℝ))
      unfold Value.Archive; apply tsum_congr; intro j; split_ifs with he; swap; · rfl
      exact Classical.not_not.mp fun ht=>hU (by rw [← he]; exact (h.labels.forced.permit _ _ ht).1)
    rw [he] at hv; simp at hv
  only:= by
    intro U W hP hF; refine congr_arg Complex.ofReal (tsum_congr fun j=>?_)
    split_ifs with he; rw [← he] at hP hF; exact h.labels.forced.reads j _ _ hP hF
    rfl
  inv:= by intro t U; apply congr_arg; unfold Value.Archive; simp_rw [fun j=> h.labels.forced.sym j t U]

lemma same_vac {σ C Λ δ w : ℝ} (Q : Rep G n) (hv : Q.Lawful σ C Λ δ w) (K : ι→Lifted G θ Q.p.threshold)
    (h : Background Q K) (i : addressKey n) : freezeKey K (hush θ i)= archived Q θ hv i := by
  refine properties rfl rfl rfl ?_
  funext U; unfold archived freezeKey; dsimp only
  rw [← h i U]; unfold Value.column
  rw [← Finset.sum_filter]; refine (Finset.sum_subtype _ ?_ (fun i=>(K i).value U)).symm
  intro j; simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [Subtype.ext_iff (a1:=name (K j)),Prod.ext_iff (x:=(name (K j)).val)]
  change _ ↔ calls (K j)=i ∧ _
  rw [Subtype.ext_iff (a1:=calls (K j))]
  exact and_comm
where
  properties {A B : Lifted G θ Q.p.threshold} (h : A.extent=B.extent) (he : A.inventory=B.inventory) (ht : A.fires=B.fires) (hp : A.value=B.value) : A=B:=by cases A;cases B;congr
-- retain choice of distinct addresses for every compatible configuration.
private lemma powered {V W E : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [CommSemiring E]
    (t : V→ W) (g : V → E) (p : Finset W) :
    ∏ i ∈ p,(∑ j : {j // t j=i},g j.val)=
      ∑ s∈ univ.filter (fun s : Finset V=>s.image t=p ∧ Set.InjOn t s), ∏ j∈s,g j := by
  let b := (i:↥p) → {j : V//t j=i.val}
  let f (x:b) (i:↥p):=(x i).val
  let m (x:b):= univ.image (f x)
  have ht (x) (i): t (f x i)=i.val:= (x i).property
  have hi (x) : Injective (f x) := fun i j h=>Subtype.ext ((ht x i).symm.trans ((congr_arg _ h).trans (ht x j)))
  have hx {y s} : s∈ m y↔∃ i,f y i=s:= by simp [m]
  have hv x: (m x).image t=p∧ Set.InjOn t (m x):= by
    constructor
    · unfold m; rw [Finset.image_image]; ext i; simp [ht]
    rintro j hj i hc h; obtain ⟨j,rfl⟩:=hx.mp hj; obtain ⟨i,rfl⟩:=hx.mp hc; congr 1; apply Subtype.ext; rw [ht,ht] at h; exact h
  have he : Injective m := by
    intro x y he; funext i; apply Subtype.ext
    obtain ⟨j,hj⟩ := hx.mp (show f x i∈ m y from he ▸ hx.mpr ⟨i,rfl⟩)
    rw [show j=i from Subtype.ext ((ht y j).symm.trans ((congr_arg t hj).trans (ht x i)))] at hj
    exact hj.symm
  rw [← Finset.prod_coe_sort, Fintype.prod_sum]; apply Finset.sum_bij (fun x _=>m x)
  · exact fun x _=> mem_filter.mpr ⟨mem_univ _,hv x⟩
  · exact fun _ _ _ _ hh=>he hh
  · intro s hs; obtain ⟨h1,h2⟩:= (mem_filter.mp hs).2
    have ht (i:↥p) : ∃ j∈s,t j=i.val:= mem_image.mp (h1.symm ▸ i.property)
    choose l hl hm using ht
    let y (i:↥p): {j // t j=i.val}:= ⟨l i,hm i⟩
    refine ⟨y, mem_univ _,Finset.ext fun i=>?_⟩; rw [hx]; constructor
    · rintro ⟨j,rfl⟩; exact hl j
    intro hh
    let v : ↥p:= ⟨t i,h1 ▸ mem_image_of_mem t hh⟩
    exact ⟨v,h2 (hl v) hh (hm _)⟩
  intro x _; unfold m; rw [Finset.prod_image (hi x).injOn]
private lemma completes (s : Finset ι) (U : Config G n) :
    Lifted.gather K s U ↔ Set.InjOn (name ∘ K) s ∧ Lifted.gather (freezeKey K) (s.image (name ∘ K)) U := by
  have hz : s.biUnion (fun i=> (K i).inventory)=(s.image (name ∘ K)).biUnion (fun i=>(freezeKey K i).inventory):= by ext i; simp [name,Function.comp_def,freezeKey,calls]
  let f:= name ∘ K
  constructor
  · rintro ⟨H,h⟩; refine ⟨?_,?_, hz.symm.trans h⟩
    · intro i hi j hj he; by_contra h0; have hx : (K i).extent=(K j).extent:= congr_arg (fun j=>(freezeKey K j).extent) he; have hr : Disjoint (K i).extent (K i).extent:= Eq.mpr (congr_arg (Disjoint (K i).extent) hx) (H hi hj h0)
      exact ((K i).needed.mono (K i).records).ne_empty (disjoint_self.mp hr)
    intro i hi j hj hq; obtain ⟨u,hu,rfl⟩:=mem_image.mp hi; obtain ⟨v,hv,rfl⟩:=mem_image.mp hj; exact H hu hv (fun h=> hq (congr_arg f h))
  rintro ⟨hh,hg,H⟩; exact ⟨fun i hi j hj hp=>hg (Finset.mem_image_of_mem f hi) (Finset.mem_image_of_mem f hj) (fun hq=>hp (hh hi hj hq)), hz.trans H⟩

lemma read_key (p : Setting θ) (U : Config G n) : (freezeKey K p).amount U=∑ i : Riders K p,(K i).amount U := by
  ext i; unfold Lifted.amount
  rw [Poly.part_sum,Poly.part_send]; change (if i=p.val.2 then _ else _) = _
  split_ifs with h
  · exact Finset.sum_congr rfl fun t _=> by rw [Poly.part_send, if_pos (show i=(K t).fires from h.trans (congr_arg (fun i : Setting θ=> i.val.2) t.property).symm)]
  symm; exact Finset.sum_eq_zero fun i _=> by rw [Poly.part_send, if_neg (fun H=>h (H.trans (congr_arg (fun i : Setting θ=> i.val.2) i.property)))]
lemma all_keys (U : Config G n) : ∑ s : Finset _,Lifted.pack K s U=∑ t,Lifted.pack (freezeKey K) t U := by
  let t:= name ∘ K; let F:=freezeKey K; let q:=fun p=> Lifted.pack K p U
  have he p : F = freezeKey K ∧ Lifted.gather K p U ↔ Set.InjOn t p ∧ Lifted.gather F (p.image t) U := by simp only [F,true_and]; exact completes K p U
  change ∑ s, q s=_
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Finset ι)) (fun p=>p.image t) q]; apply Finset.sum_congr rfl; intro i _
  unfold Lifted.pack; split_ifs with H
  · simp_rw [read_key]; change _= ∏ j∈ i,∑ u : {s // t s=j}, (K u.val).amount U
    rw [powered (g:=fun i=>(K i).amount U)]; simp_rw [sum_filter]
    apply sum_congr rfl; intro a _; unfold q Lifted.pack
    split_ifs <;> grind
  apply Finset.sum_eq_zero; intro j hj; unfold q Lifted.pack; rw [if_neg]
  have ht := (mem_filter.mp hj).2
  intro he; exact H (ht ▸ ((completes K j U).1 he).2)
end YM.PhysicalNext.InteractingRank.Gel

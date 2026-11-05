import YM.Next.FREE_KERNELS.SingleAxis

/-!
# One axis step of exterior row homotopy

Positive exterior degree. Rows still with one momentum group (Cover signs).
Cycles on all mesh points can instead be checked on baseCube. No global
Laurent current from a single finite mesh. We include the weighted budget
for a choice independent of the price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open Work.F06 (addAxis remove_addAxis addAxis_remove notMem_cut mem_addAxis parity_square)
open scoped Topology BigOperators ComplexConjugate

variable {m n k : Type*}

def constantRows (A : Matrix m n ℝ) := fun (i : m) (j : n) (x : Cover) => A i j*token 0 x
lemma constant_whole [Fintype m] [Fintype n] (A : Matrix m n ℝ) : Whole (constantRows A) := by
  obtain ⟨C,hC,h⟩ := Work.F06.strip_of_fin {0} (constantRows A) (fun i j x h => by simp [constantRows,token,show x≠0 from by simpa using h]) 1
  exact ⟨1,C,one_pos,h⟩
lemma constant_read (A : Matrix m n ℝ) (p : Momentum) : Row.read (constantRows A) p=approached A := by
  ext i j
  let k (x : Cover) := (token 0 x:ℂ)
  simp only [approached,Row.read,Matrix.of_apply,constantRows,Laurent.read,Complex.ofReal_mul,smul_eq_mul, Matrix.map_apply]
  have he : ∑' x,mode p x*k x = mode p 0 := token_eval 0 p
  simp_rw [mul_left_comm (mode p _),tsum_mul_left]; rw [he,mode_zero,mul_one]

lemma left_crank (r : ℕ) (k : Axis) : approached (left ℝ r k)=left ℂ r k := by
  ext i j; simp only [approached, Exterior.left,Matrix.of_apply,Matrix.map_apply]
  split_ifs <;> simp_all [parity]

lemma switch_axis {x : Axis} (p : Momentum) : q p x=chip (p x) := rfl
lemma renew_q [TopologicalSpace m] [T2Space m] (f g : Momentum → m) (k : Axis)
    (hf : ∀ p∈baseCube, ContinuousAt f p) (hg : ∀ p∈baseCube, ContinuousAt g p)
    (h : ∀ p∈baseCube,q p k≠0 → f p=g p) (p : Momentum) (hp : p ∈ baseCube) : f p = g p := by
  by_cases he : p k≠0
  · apply h p hp; rw [switch_axis]
    apply norm_pos_iff.mp ((mul_pos meter.low_pos (norm_pos_iff.mpr he)).trans_le _)
    exact meter.below _ (zone_in_disk p (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) _)
  have h₀ := not_ne_iff.mp he
  let v (t : ℝ) : Momentum := Function.update p k (t:ℂ)
  have hv : v 0=p := by unfold v; simp [← h₀, Function.update_eq_self]
  have hc : Continuous v := continuous_pi fun i => by unfold v; by_cases h : i=k <;> simp [Function.update,h, Complex.continuous_ofReal]; exact continuous_const
  let F := 𝓝[>] (0:ℝ)
  have hx : Tendsto v F (𝓝 p) := hv ▸ (hc.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have heq : f ∘ v =ᶠ[F] g ∘ v := by
    filter_upwards [self_mem_nhdsWithin (a:=0) (s:=Ioi 0), mem_nhdsWithin_of_mem_nhds (gt_mem_nhds Real.pi_pos)] with u hu hz
    have hu' : 0<u := hu
    have hz' : u < Real.pi := hz
    have hb : v u ∈ baseCube := by
      refine ⟨(physical_iff _).mpr ?_,?_⟩
      · intro i; by_cases h : i=k
        · simp [v,h]
        simpa [v,h] using (physical_iff _).mp hp.1 i
      intro i; by_cases h : i=k
      · simp [v,h,abs_of_pos hu',hz'.le]
      simpa [v,h] using hp.2 i
    apply h _ hb; rw [switch_axis]
    exact norm_pos_iff.mp ((mul_pos meter.low_pos (norm_pos_iff.mpr (by simp [v,hu'.ne']))).trans_le
      (meter.below _ (zone_in_disk (v u) (mem_cube_real (base_subset_realCube zone_pos hb) zone_pos) k)))
  exact tendsto_nhds_unique (((hf _ hp).tendsto.comp hx).congr' heq) ((hg _ hp).tendsto.comp hx)

lemma read_here (R : Row m n) (h : Whole R) {p : Momentum} (hp : p∈baseCube) : ContinuousAt R.read p := by
  change ContinuousAt (fun p i j => Laurent.read (fun x => (R i j x:ℂ)) p) p
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  obtain ⟨σ,C,hp',h⟩ := h
  have he := Work.F07.realStrip (σ/2) (by linarith) hp.1
  exact (Work.F07.readDeriv (Row.constant_strip R h i j) (by linarith) (by linarith) he).1.continuousAt

variable {ι : Type*} {r : ℕ}

/-- Right cycle: second argument contracted by q. -/
def Reigned (r : ℕ) (A : Row m (TypeFace (r+1))) : Prop := ∀ p∈baseCube,A.read p*symbol r p=0

def pending (s : Axis) (A : Row m n) : Row m n := fun i j => payOut (zeroAxis s) (A i j)
def dashAxis (s : Axis) (A : Row m n) : Row m n := fun i j => payOut (partAxis s) (A i j)
def relief (s : Axis) (r : ℕ) (A : Row m (TypeFace (r+1))) :=
    composeRows (dashAxis s A) (constantRows (left ℝ (r+1) s).transpose)
def shed (s : Axis) (r : ℕ) (A : Row m (TypeFace (r+1))) : Row m (TypeFace (r+1)) := fun i j =>
    if s∈j.val then (fun _ => 0) else pending s A i j

section budgets
variable {w : ι → ℝ} {α β : ι → Type*}
lemma pending_stock {A : ∀ i, Row (α i) (β i)} (h : Stock w A) (s : Axis) : Stock w fun i => pending s (A i) := by
  refine ⟨h.cash,?_⟩; obtain ⟨η,C,he,hc,h⟩ := h.uniform
  exact ⟨η,C,he,hc,fun i a b => by unfold pending; simpa only [one_mul] using (eval_axis η he.le s).released zero_le_one (h i a b) he.le⟩
lemma dash_stock {A : ∀ i, Row (α i) (β i)} (h : Stock w A) (s : Axis) : Stock w fun i => dashAxis s (A i) := by
  refine ⟨h.cash,?_⟩; obtain ⟨η,C,he,hc,h⟩ := h.uniform
  refine ⟨η/2,(η/2)⁻¹*C,by positivity,by positivity,fun i a b => ?_⟩
  rw [mul_assoc]; exact (dividend η he s).released (by positivity) (h i a b) (by positivity)

lemma dash_whole {A : Row m n} (h : Whole A) (s : Axis) : Whole (dashAxis s A) :=
  (dash_stock (Stock.constant (ι:=Unit) A h) s).whole ()

lemma relief_stock {A : ∀ i, Row (α i) (TypeFace (r+1))} (h : Stock (α:=α) (β:=fun _ => TypeFace (r+1)) w A) (s : Axis) : Stock (α:=α) (β:=fun _ => TypeFace (r+1+1)) w fun i => relief s r (A i) := by
  have hD := dash_stock h s
  let B := constantRows (left ℝ (r+1) s).transpose; have he : Whole B := constant_whole _
  have hh := Stock.times hD (Stock.constant B he); simp only [mul_one] at hh; exact hh
lemma shed_stock {A : ∀ i, Row (α i) (TypeFace (r+1))} (h : Stock (α:=α) (β:=fun _ => TypeFace (r+1)) w A) (s : Axis) : Stock (α:=α) (β:=fun _ => TypeFace (r+1)) w fun i => shed s r (A i) := by
  refine ⟨h.cash,?_⟩; obtain ⟨η,C,hp,hc,H⟩ := (pending_stock h s).uniform
  refine ⟨η,C,hp,hc,fun i a b => ?_⟩; unfold shed; split
  · simp [Laurent.Width,SumBudget,mul_nonneg hc.le (h.cash i)]
  exact H i a b
lemma relief_whole (s : Axis) {A : Row m (TypeFace (r+1))} (h : Whole A) : Whole (relief s r A) :=
  (relief_stock (Stock.constant (ι:=Unit) A h) s).whole ()
lemma shed_whole (s : Axis) {A : Row m (TypeFace (r+1))} (h : Whole A) : Whole (shed s r A) :=
  (shed_stock (Stock.constant (ι:=Unit) A h) s).whole ()
end budgets

lemma read_blank {A : Row m n} (h : Whole A) (s : Axis) {p : Momentum} (hp : physical p) :
    (pending s A).read p=A.read (update p s 0) := by
  obtain ⟨η,C,hp',H⟩ := h; ext i j; exact retuned (H _ _) hp' _ hp
lemma read_part {A : Row m n} (h : Whole A) (s : Axis) {p : Momentum} (hp : physical p) :
    q p s • (dashAxis s A).read p=A.read p-A.read (update p s 0) := by
  obtain ⟨η,C,hp',H⟩ := h; ext i j; exact single_axis (H _ _) hp' _ hp
lemma read_before {A : Row m (TypeFace (r+1))} (h : Whole A) (s : Axis) {p : Momentum} (hp : physical p) :
    (relief s r A).read p = (dashAxis s A).read p*(left ℂ (r+1) s).transpose := by
  unfold relief; rw [(dash_whole h s).read (constant_whole _) hp,constant_read]; congr 1
  have he : ∀ A : Matrix (TypeFace (r+1+1)) (TypeFace (r+1)) ℝ, approached A.transpose=(approached A).transpose := fun _ => rfl
  rw [he,left_crank]

lemma projection_axis (r) (s : Axis) : left ℂ r s * (left ℂ r s).transpose=Matrix.diagonal fun a => if s∈a.val then 1 else 0 := by
  ext i j
  rw [Matrix.diagonal_apply]; change (left ℂ r s *ᵥ (fun k => (left ℂ r s) j k)) i= _
  rw [Exterior.eliminate]; by_cases h : s∈i.val
  · rw [dif_pos h]; by_cases ht : i=j
    · subst j; unfold left; simp only [Matrix.of_apply,if_true,h]; exact parity_square (R:=ℂ) ..
    unfold left; rw [Matrix.of_apply,if_neg ht]
    split_ifs with he hg
    · exact False.elim (ht (by
        apply Subtype.ext
        have hi := Finset.insert_erase h
        have hj := Finset.insert_erase he
        have hz := congr_arg Subtype.val hg
        unfold Exterior.remove at hz
        change j.val.erase s=i.val.erase s at hz
        rw [← hi,← hz,hj]))
    all_goals simp
  rw [dif_neg h]; split <;> simp [*]

lemma read_shed {A : Row m (TypeFace (r+1))} (h : Whole A) (s : Axis) {p : Momentum} (hp : physical p) :
    (shed s r A).read p=A.read (update p s 0)*(1-left ℂ r s*(left ℂ r s).transpose) := by
  rw [projection_axis, Matrix.mul_sub,Matrix.mul_one,← read_blank h s hp]; ext i j; rw [Matrix.sub_apply,Matrix.mul_diagonal]; by_cases hh : s∈j.val
  · simp [shed,hh,Row.read,Laurent.read]
  rw [if_neg hh,mul_zero,sub_zero]; simp only [Row.read,of_apply,shed,hh,if_false]

lemma breaks_symbol (r : ℕ) (s : Axis) (p : Momentum) : symbol r p=symbol r (update p s 0)+q p s • left ℂ r s := by
  have he i : q p i=q (update p s 0) i+(if i=s then q p i else 0) := by by_cases hi : i=s <;> simp [hi,q,Function.update]
  unfold symbol wedge; conv_lhs => arg 2; intro i; rw [he]
  simp only [add_smul,Finset.sum_add_distrib,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

lemma success {A : Row m (TypeFace (r+1))} (h : Whole A) (s : Axis) (hr : Reigned r A) (p : Momentum) (hp : p∈baseCube) :
    (relief s r A).read p*symbol (r+1) p+(shed s r A).read p = A.read p := by
  apply renew_q (fun p => (relief s r A).read p * symbol (r+1) p+(shed s r A).read p) (Row.read A) s _ _ _ p hp
  · intro p he
    have hh : Continuous (symbol (r+1)) := by unfold symbol wedge Exterior.q; fun_prop
    let f := (relief s r A).read
    have hc := read_here _ (relief_whole s h) he
    have hfg : ContinuousAt (fun q => f q * symbol (r+1) q) p := by
      change ContinuousAt (fun q i j => ∑ k : TypeFace (r+1+1), f q i k*symbol (r+1) q k j) p
      apply continuousAt_pi.mpr; intro i; apply continuousAt_pi.mpr; intro j
      refine tendsto_finsetSum (f:=fun k q => f q i k*symbol (r+1) q k j) _ fun k _ => ?_
      apply Filter.Tendsto.mul; exact continuousAt_pi.mp (continuousAt_pi.mp hc i) k; exact continuousAt_pi.mp (continuousAt_pi.mp hh.continuousAt k) j
    exact hfg.add (read_here _ (shed_whole s h) he)
  · exact fun p => read_here A h
  intro p hp hc
  rw [read_before h s hp.1,Matrix.mul_assoc]
  let M := A.read (update p s 0)
  let D := symbol r p; let W := symbol (r+1) p
  let L := left ℂ r s; let L' := left ℂ (r+1) s
  let Q := q p s
  have hb : L'.transpose * W = Q • 1-D*L.transpose := by
    apply eq_sub_iff_add_eq.mpr; rw [add_comm (_*W)]; exact cartan_entry r (q p) s
  have hx : M*D=Q • (M*L) := by
    rw [show D=_ from breaks_symbol r s p, Matrix.mul_add, Matrix.mul_smul,show M*symbol r (update p s 0)=0 from hr _ (bank_blank hp s),zero_add]
  let R := A.read p
  have hm : q p s • ((relief s r A).read p*W)=q p s • (R-M*(1-L*L.transpose)) := by
    rw [read_before h s hp.1,Matrix.mul_assoc,← Matrix.smul_mul,read_part h s hp.1]
    change (R-M)*(L'.transpose*W)=_
    rw [hb]; simp only [Matrix.mul_sub,Matrix.sub_mul, Matrix.mul_smul,Matrix.mul_one,
      ← Matrix.mul_assoc,show R*D=0 from hr _ hp,hx,Matrix.zero_mul,Matrix.smul_mul,smul_sub]; abel
  rw [← read_shed h s hp.1] at hm
  rw [← Matrix.mul_assoc,← read_before h s hp.1]; exact eq_sub_iff_add_eq.mp (smul_right_injective _ hc hm)
end YM.Next.Free

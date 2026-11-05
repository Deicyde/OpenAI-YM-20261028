import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Binding
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Leading

/-! # Price and color proofs on Rank curves. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Rise Spindle Atlas WeightedGaussianMarginal45C.Issue.Cut
    AnalyticBridge.LocalGaussianLaws Work.F08 FreeResolvent Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge}
section linear
variable {α β : Type} [Fintype α] [Fintype β]
omit [Fintype α] in
lemma linear_write {p : α → β→₀ℂ} (f : β → ℂ) (i : α) : Normal.reads p f i=∑ j, p i j * f j := by
  unfold Normal.reads; exact Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ) (by simp)
lemma coin_pay (x : β →₀ ℂ) : coin (Normal.glyph x) ≤ ∑ j, ‖x j‖ := by
  rw [show Normal.glyph x = ∑ i, x i • MvPolynomial.X i from Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ) (by simp)]
  apply (Rise.collect _ (show 0 ≤ (1:ℝ) from zero_le_one) _ _).trans
  refine Finset.sum_le_sum fun i _=>?_
  simpa only [Rise.pay_X,one_pow,mul_one] using LiftMark.peak_cost 1 0 (x i) (MvPolynomial.X i) zero_le_one
omit [Fintype α] in
lemma scope_price (Q : Normal.Symmetric β) {a c : ℝ} (C : α→β→₀ℂ) (h : ∀ i, ∑ j, ‖C i j‖ ≤ a) (ha : 0≤a) (hc : 0≤c)
    (he : ∀ i j, ‖Q.cov i j‖ ≤ c) (x y) :
    ‖(Normal.scope C Q).cov x y‖ ≤ a^2*c := by
  let f (i) := ∑ j, C x j*Q.cov j i
  have hf : (Finsupp.linearCombination ℂ Q.cov (C x)) = f := by
    rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ) (by simp)]
    funext i; exact Finset.sum_apply ..
  have hv i : ‖f i‖ ≤ a*c := by
    apply (norm_sum_le ..).trans
    simp_rw [norm_mul]
    refine (sum_le_sum (g:=fun j => ‖C x j‖ * c) fun j _ => ?_).trans ?_
    · exact mul_le_mul_of_nonneg_left (he _ _) (norm_nonneg _)
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h _) hc
  change ‖Normal.treats Q _ _‖≤_
  unfold Normal.treats; rw [hf, Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ) (by simp)]
  apply (norm_sum_le ..).trans; simp_rw [smul_eq_mul,norm_mul]
  refine (sum_le_sum (g:=fun j => ‖C y j‖ * (a*c)) fun j _ => mul_le_mul_of_nonneg_left (hv _) (norm_nonneg _)).trans ?_
  rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right (h _) (mul_nonneg ha hc)).trans_eq (by ring)

open ColorBook
private def hue (t : G.El) (i j : G.ColorIndex) : ℂ := ((G.adjoint t) ((EuclideanSpace.basisFun _ ℝ) j) i:ℝ)
private lemma hue_unit (t : G.El) (i j : G.ColorIndex) : (∑ k, hue t i k*hue t j k) = if i=j then 1 else 0 := by
  let L := tagColor (fun _ : Unit=> adBody t) ()
  have he : L*L.transpose=1 := mul_eq_one_comm.mp ((tag_checked (fun _ : Unit=> adBody t)) ())
  have hu a b : hue t a b=(L a b:ℂ) := by
    let v := (EuclideanSpace.basisFun G.ColorIndex ℝ) b
    suffices hx : L a b=(adBody t v).ofLp a by rw [hx]; rfl
    have hx := congr_fun (tag_runs (fun _ : Unit=> adBody t) v ()) a
    change (L *ᵥ v.ofLp) a=_ at hx
    rw [show v.ofLp=Pi.single b 1 from ?_, Matrix.mulVec_single_one] at hx
    · exact hx
    ext q; simp [v, Pi.single_apply,eq_comm]
  simp_rw [hu,← Complex.ofReal_mul]; rw [← Complex.ofReal_sum, ← show (L*L.transpose) i j=∑ k,L i k*L j k from Matrix.mul_apply ..,he]
  by_cases h : i=j <;>simp [h,Matrix.one_apply]

omit [Fintype α] [Fintype β] in
private lemma color_frame {i j : α} (a b : G.ColorIndex) (t : G.El) (p : α→G.ColorIndex→β) (X : Normal.Symmetric β) (s : α→α→ℂ)
    (h : ∀ (i j : α) a b,X.cov (p i a) (p j b) = if a=b then s i j else 0) :
    Normal.treats X (∑ z, Finsupp.single (p i z) (hue t a z)) (∑ z,Finsupp.single (p j z) (hue t b z))=X.cov (p i a) (p j b) := by
  unfold Normal.treats
  simp only [map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [h]; simp only [mul_ite,mul_zero,sum_ite_eq',mem_univ,↓reduceIte]
  calc
    _ = (∑ z,hue t a z*hue t b z)*s i j := by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun z _=>?_ ; ring
    _ = _ := by rw [hue_unit]; split <;> simp
end linear

variable {C : Family G} (B : Binding C) {N i p : ℕ}
local notation "X" => stamp C.path.levels N p
variable (h : i < N)

private lemma expand_tint {c f : Side} (P : Matrix (Body 2 c) (Body 2 f) ℝ) (i : Incidence G c) (j : Incidence G f) :
    (tensor G P (toPAC i) (toPAC j):ℂ) = if i.2.2 = j.2.2 then (P (i.1,plaquette i.2.1) (j.1,plaquette j.2.1):ℂ) else 0 := by
  by_cases h : i.2.2=j.2.2 <;> simp [tensor,toPAC,h,plaqEquiv]

lemma speaks (u) (i : ℕ) (N p : ℕ) :
    let Q:= Normal.exchange (short B N p i).H
    Q.comp (Normal.exchange (coloration (C.side (i+1) p) u))=(Normal.exchange (coloration (C.side i p) u)).comp Q := by
  intro Q
  ext1 i'
  simp only [Q,AlgHom.comp_apply,Normal.exchange_x]
  let P := shorter B N i
  let T:= installed (C.path.levels.clock.op i p).ratio P
  have he (a b) : (short B N p i).H a b= if a.2.2=b.2.2 then (T (a.1,plaquette a.2.1) (b.1,plaquette b.2.1):ℂ) else 0 := by
    rw [H_at]; exact expand_tint T a b
  let s (y : Site (C.side i p)) (k : PlaqAxes) := ((T (i'.1,plaquette i'.2.1) (y,plaquette k)) : ℂ)
  -- expand H as sum over position indices, then commute with the color action
  have hz z : Normal.glyph ((short B N p i).H (i'.1,i'.2.1,z)) = ∑ y, ∑ k,s y k • MvPolynomial.X (y,k,z) := by
    rw [Normal.glyph,Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ) (by simp),Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _=>?_; rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _=>?_
    simp only [he,ite_smul,zero_smul,sum_ite_eq,mem_univ,↓reduceIte]; rfl
  unfold coloration; rw [map_sum, map_sum, show Normal.glyph ((short B N p i).H i') = _ from hz i'.2.2, map_sum]
  simp only [Finsupp.linearCombination_single,_root_.map_smul,Normal.exchange_x,hz,Finset.smul_sum,map_sum,Finsupp.linearCombination_single]
  -- reorder
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
  exact Finset.sum_congr rfl fun j _=>smul_comm ..

lemma exact_voice (i p) (h : i<N) : Voice (short B N p) i := by
  refine ⟨fun u => speaks B u i N p,fun u => ?_⟩
  let c:= C.side (i+1) p; let k:= Current.fConditional (C.path.levels.clock.op i p) (B.world.H N (i+1)) (B.world.H N i) (B.world.towers N i); let T := (short B N p i).Q
  let r := (C.path.levels.clock.op i p).ratio.parent
  let l := C.path.levels.clock.hatBeta i
  let S' (i j : Pressure.Cell c) : ℂ := if separation (r i.1) (r j.1) ≤ lastHem l then
       (k (i.1,plaquette i.2) (j.1,plaquette j.2):ℂ) else 0
  let m (t : Pressure.Cell c) (z : G.ColorIndex) : Incidence G (C.side (i+1) p) := (t.1,t.2,z)
  have he i' j a b : T.cov (m i' a) (m j b)= if a=b then S' i' j else 0 := by
    unfold T m short Qrow
    dsimp only
    rw [planner_Q B _ _ _ h, expand_tint]
    by_cases hr : a=b <;> simp [hr,S',k,l,r,ite_self]
  apply Normal.Symmetric.ext; funext i' j; rcases i' with ⟨v,w,a⟩; rcases j with ⟨q,r,b⟩
  exact color_frame a b u m T S' he (i:=(v,w)) (j:=(q,r))

lemma inked (a b : ℕ) (h : 4*a ≤ b) : Spindle.Stamped a b i X h := by
  let Q := Atlas.control X 0 b (k:=i); let n := C.side i p
  let W : (Spindle.slotC G a) → _ := fun z => body (P:=C.S) (k:=i) (p:=p) 0 (calls h z).val
  let P := Normal.scope (fun i : slotC G a => Finsupp.single (calls h i) 1) Q
  constructor
  · intro i' j
    unfold Atlas.control; rw [Normal.match_name,stamp_pairs]; simp
  intro u T
  let M := scalarCov C.path.levels.clock.kernel.penalty (Next.Free.location C.path.levels N i) n
  let S' (x y : Turn a) : ℂ := M (wrap n (0 + x.val.1), plaquette x.val.2) (wrap n (0 + y.val.1),plaquette y.val.2)
  have ht i' j : T.cov i' j = ((stamp C.path.levels N p).κ i).cov (W i') (W j) := by
    unfold T Atlas.control
    simp_rw [Normal.match_name]; rfl
  apply Normal.Symmetric.ext; funext i' j
  obtain ⟨q,k⟩:=i'
  obtain ⟨v,l⟩:=j
  have he (x y : Turn a) (i' j : G.ColorIndex): P.cov (x,i') (y,j) = if i'=j then S' x y else 0 := by
    change T.cov _ _ = _
    rw [ht, stamp_pairs,complete,expand_tint]; rfl
  exact color_frame k l u Prod.mk P S' he

-- Bounds reserved before block lengths. `Purse.L` should buy these.
def capital (K : KernelChoices) (Z : MapPrices) (j : ℕ) :=
    let b := ticket (TypeFace 2) (psiBudget (Z.Ω j))
    let c := max 0 ((RankCovariance.prepared K).centers j)
    max 1 (max b (c+b^2*c))

def optics (Y : Levels G) (k D : ℕ) :=
    (RankCovariance.prepared Y.clock.kernel).centers (Y.clock.J k) ≤ LiftMark.tin (Atlas.clim Y k) D

lemma producesInk (D : ℕ) (h : optics C.path.levels i D) : Next.Rank.Ribbon.Hail C i p D X := by
  unfold Next.Rank.Ribbon.Hail
  intro A b Q
  refine ⟨fun H=>inked _ _ H,fun j k=>?_⟩
  unfold Q Atlas.control
  rw [Normal.match_name, ← stamp_real C.path.levels N i p,Complex.norm_real,Real.norm_eq_abs]
  exact ((RankCovariance.prepared A.clock.kernel).earns _ (A.clock.adm _) A rfl N i p rfl _ _).trans h

lemma paths_budget (hI : i < N) (hJ : C.path.levels.clock.J (i+1)=C.path.levels.clock.J i) (d : ℝ)
    (hd : capital C.path.levels.clock.kernel B.prices (C.path.levels.clock.J i) ≤ d) :
    (short B N p i).Fair d ∧ (track X i).Fair d := by
  let A:= C.path.levels; let J:= A.clock.J i; let c := max 0 ((RankCovariance.prepared A.clock.kernel).centers J); let z := B.prices.Ω J
  let a:= psiBudget z; let b:= ticket (TypeFace 2) a
  let S:=short B N p i; let T:=track X i
  have he : ∀ q, q ≤ N → 0 ≤ B.prices.Ω (A.clock.J q) := by
    intro q hq; let k := plaquette ⟨(0,1),by decide⟩; have he := ((B.pays.rows N q hq).1 k k)
    exact (tsum_nonneg he.1).trans he.2.2
  have hj : 0≤c := le_max_left ..
  have hz:= he i hI.le
  have ha: 0 ≤ a := psiBudget_nn z hz
  have hb: 0 ≤ b := ticket_nonneg _ ha
  let r:=((C.S.block i).val:ℝ)
  have hx : 1 ≤ r := by unfold r; exact_mod_cast (show 1 ≤ _ from Nat.succ_le_of_lt (C.S.block i).property)
  have hr : ticket (TypeFace 2) (a/r^2) ≤ b := by unfold b ticket; gcongr; exact div_le_self ha (one_le_pow₀ hx)
  have hc u : (∑ v, ‖T.H u v‖) ≤ b := (high_rows B hI hJ u).1.trans hr
  have hP j (hp:A.clock.J j=J) (i v : Chamber G A.S j p) : ‖((stamp A N p).κ j).cov i v‖ ≤ c := by
    rw [← stamp_real A N j p,Complex.norm_real,Real.norm_eq_abs]
    exact ((RankCovariance.prepared A.clock.kernel).earns _ (hp ▸ A.clock.adm _) A rfl N j p hp i v).trans (le_max_right ..)
  obtain ⟨h',hb',hv⟩:= show 1≤d ∧ b≤d ∧ c+b^2*c≤d by
    unfold capital at hd; rcases max_le_iff.mp hd with ⟨h,hq⟩; exact ⟨h,max_le_iff.mp hq⟩
  have hf : T.Fair d := {
    positive:=h'
    charge := fun i => ((coin_pay _).trans (hc i)).trans hb'
    tide := fun u v=> by
      apply le_trans _ hv
      change ‖((stamp A N p).κ (i+1)).cov u v+ - (Normal.scope T.H ((stamp A N p).κ i)).cov u v‖ ≤ _
      apply (norm_add_le ..).trans
      rw [norm_neg]; exact add_le_add (hP _ hJ _ _) (scope_price _ _ hc hb hj (hP i rfl) u v)
  }
  refine ⟨⟨h',fun u=> ((coin_pay _).trans ((exact_short_price B (B.prices.alpha_pos J) (sufficient_rows B hI hJ) u).trans hr)).trans hb', fun u v =>?_⟩,hf⟩
  unfold short Qrow; dsimp only
  split
  · exact hf.tide u v
  rw [norm_zero]; exact zero_le_one.trans h'
end YM.PhysicalNext.InteractingRank

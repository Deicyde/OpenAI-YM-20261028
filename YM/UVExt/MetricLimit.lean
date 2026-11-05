import YM.UVExt.FreeSymbol
import Mathlib.Analysis.Normed.Group.Tannery

/-! Fixed-level pulse and modified metric shape limits, including faithfulness of the full
finite-period test on coefficient correlations over the countably supported Laurent rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.UV
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG
open Work.F08
open scoped Classical Topology BigOperators ComplexConjugate
variable {G : Gauge} (A : Levels G) {k l : ℝ} {m : ℕ} {p : Momentum}

def vaultLim (k : ℝ) (m : ℕ) (p : Momentum) := if p=0 then (1:Frequency 2 2) else
    (∑ a : Axis, jewel 1 p a / radial A m a k p) • mask 2 (fun i=>radial A m i k p)

lemma vault_limit (hk : 0<k) (hp : p∈baseCube) :
    Tendsto (fun i=> vault k (location A i m) p) atTop (𝓝 (vaultLim A k m p)) := by
  by_cases h : p=0
  · simp only [vaultLim,h,vault_zero,↓reduceIte]; exact tendsto_const_nhds
  unfold vaultLim; simp_rw [if_neg h,vault_sources _ hk _ (base_subset_realCube zone_pos hp) h]
  have ht : Tendsto (fun i=>(location A i m).rho k p) atTop
      (𝓝 (∑ a : Axis, jewel 1 p a / radial A m a k p)) := by
    refine tendsto_finsetSum _ fun a _ => tendsto_const_nhds.div (tends_D A m a hp h) ?_
    exact fun hz => by simpa [hz,hk.not_ge] using radial_nonzero A m a hk hp h
  apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
  change Tendsto (fun u=> (Train.rho k (location A u m) p)* (mask 2 (fun a=> _) i j)) _ (𝓝 ((∑ a : Axis, _) * (mask 2 (fun a=>_) i j)))
  refine ht.mul ?_
  simp_rw [mask,Matrix.diagonal_apply]; by_cases hx : i=j
  · simp only [if_pos hx,inventory]; apply tendsto_finsetProd; intro c _; exact tends_D A m c hp h
  simp only [if_neg hx]; exact tendsto_const_nhds

section finite
variable (n : Side)
local notation "M" => Body 2 n
-- use raw rotation rather than UV-mosaic private
private def mosaic (sk : Momentum → Frequency 2 2) : Matrix M M ℂ :=
    ((n.val:ℂ)^4)⁻¹ • (rotations n (TypeFace 2) * fiber (fun x : Site n => sk (mon x)) * star (rotations n (TypeFace 2)))

def blueInf (k : ℝ) (m : ℕ) := mosaic n (vaultLim A k m)

private lemma slate_frame {j : ℕ} (hk : 0<k) (hv : 4≤j) (v : Train j) : approached ((blue k v).acts n)=mosaic n (vault k v) := by
  apply cancel_rotation n
  have hr := (heart_true k hk hv v).2
  have h := circulant n (record (vault k v)) hr.safe
  simp_rw [hr.echo (mon _) (mon_mem n _)] at h
  let F := rotations n (TypeFace 2)
  change approached ((record _).acts n) * _ = mosaic _ _ * F; rw [h]; symm
  change (((n.val:ℂ)^4)⁻¹ • ((F * fiber _)*star F)) * F=F * _
  have hC : star F*F=(n.val:ℂ)^4 • 1 := (rotations_crew n _).2.2
  rw [Matrix.smul_mul, Matrix.mul_assoc (F * fiber _),hC,Matrix.mul_smul,smul_smul]
  rw [inv_mul_cancel₀ (pow_ne_zero 4 (Nat.cast_ne_zero.mpr <| Nat.ne_of_gt n.property)), one_smul, Matrix.mul_one]

lemma slate_limit (hk : 0 < k) (a i : M) : Tendsto (fun N=> (blue k (location A N m)).acts n a i) atTop (𝓝 (((blueInf A n k m).map Complex.re) a i)) := by
  have hx := tends_mosaic n (fun i=>vault k (location A i m)) (vaultLim A k m) fun p hp => vault_limit A hk hp
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hx a) i)
  apply h.congr; intro N; have he := slate_frame n hk (A.clock.adm m) (location A N m)
  exact show (mosaic n _ a i).re = _ from (congr_arg (fun x : Matrix _ _ ℂ => (x a i).re) he.symm).trans rfl

end finite


section tools
variable {ι : Type*} {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ] {R T U : Row β γ} {D σ : ℝ}

def flotilla (σ D : ℝ) (x : Cover) := D * Real.exp (-σ * Laurent.size x)

lemma flot_summable (hs : 0 < σ) : Summable (flotilla σ D) := ((Laurent.Width.compactPay σ hs).2.1.mul_left D)

lemma width_flot (h : R.strip σ D) (a b x) : ‖R a b x‖ ≤ flotilla σ D x := by
  let c (i : Cover) := Real.exp (σ * Laurent.size i) * ‖R a b i‖
  have he := h a b
  have hc : c x ≤ ∑' i, c i := Summable.le_tsum he.2.1 _ (fun i _=>by apply he.1)
  have hx := hc.trans (show (∑' i, c i) ≤ D from he.2.2)
  change _ ≤ D * Real.exp _
  rw [neg_mul, Real.exp_neg, ←div_eq_mul_inv]; apply (le_div_iff₀' (Real.exp_pos _)).mpr hx

theorem extract_rows {f : ℕ → Row β γ} 
    (H : ∀ a b x, ∃ C : ℝ, ∀ i, ‖f i a b x‖≤C) :
    ∃ g : Row β γ, ∃ k : ℕ → ℕ, StrictMono k ∧ Tendsto (fun i=> f (k i)) atTop (𝓝 g) := by
  choose C hC using H
  let v : ℕ → ∀ a b x, Set.Icc (-C a b x) (C a b x) := fun i a b x=>⟨f i a b x, (abs_le.mp (hC a b x i))⟩
  haveI := fun a b (x : Cover) => (show CompactSpace (Set.Icc (-C a b x) (C a b x)) by infer_instance)
  obtain ⟨g,_,k,hk,ht⟩ := (isCompact_univ_iff.mpr (inferInstance : CompactSpace (∀ a b x, Set.Icc (-C a b x) (C a b x)))).tendsto_subseq (x:=v) (by simp)
  exact ⟨fun a b x=> (g a b x).val,k,hk,tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b => tendsto_pi_nhds.mpr fun x=>
     (continuous_subtype_val.tendsto _).comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht a) b) x)⟩

variable {F : Filter ι}
lemma tendsto_entries {f : ι → Row β γ} {g : Row β γ} (ht : Tendsto f F (𝓝 g)) (hs : 0<σ) (he : ∀ᶠ i in F, (f i).strip σ D) (n : Side) :
    Tendsto (fun N=> (f N).acts n) F (𝓝 (g.acts n)) := by
  refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> tendsto_tsum_of_dominated_convergence (flot_summable hs (D:=D)) (fun x => ?_) ?_
  · by_cases h : j.1=i.1+wrap n x
    · simp_rw [if_pos h]; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht i.2) j.2) x
    simp_rw [if_neg h]; exact tendsto_const_nhds
  filter_upwards [he] with N h; intro x; split
  · exact width_flot h _ _ _
  rw [norm_zero]; exact (norm_nonneg ((f N i.2 j.2 x))).trans (width_flot h i.2 j.2 _)

lemma restore_coeff {D : ℕ→Side} (h : Tendsto (fun i=> (D i).val) atTop atTop) (hv : ∀ c d, Summable fun x=> ‖R c d x‖) (a b x) :
    Tendsto (fun i=> R.acts (D i) (0,a) (wrap _ x,b)) atTop (𝓝 (R a b x)) := by
  let f (y : Cover) := if y=x then R a b x else 0
  have he i : R.acts (D i) (0,a) (wrap (D i) x,b)=∑' t : Cover, if wrap (D i) t=wrap _ x then R a b t else 0 := by simp only [Row.acts,zero_add,Matrix.of_apply,eq_comm]
  have hx : R a b x = ∑' t, f t := by rw [tsum_eq_single x (fun t h=>if_neg h)]; simp
  conv_rhs => rw [hx]
  rw [show (fun i=>R.acts (D i) (0,a) (wrap (D i) x,b))=fun _=>_ from funext he]
  refine tendsto_tsum_of_dominated_convergence (hv a b) (fun t=> tendsto_const_nhds.congr' ?_) (by filter_upwards [] with i t; split <;> simp)
  by_cases ht : t=x
  · exact (Eventually.of_forall (fun i => by simp [f,ht]))
  obtain ⟨j,hj⟩ := Function.ne_iff.mp ht
  filter_upwards [h.eventually (eventually_gt_atTop (x j - t j).natAbs)] with i hi
  have hg : wrap (D i) t ≠ wrap (D i) x := by
    intro he
    have hD := ZMod.intCast_eq_intCast_iff_dvd_sub (t j) (x j) _ |>.mp (congr_fun he j)
    have hw : (D i).val ≤ (x j - t j).natAbs := Nat.le_of_dvd (by omega) (show _ from Int.ofNat_dvd_left.mp hD)
    omega
  simp [f,ht,hg]

lemma restore_rows {D : ℕ→Side} (h : Tendsto (fun i=> (D i).val) atTop atTop) (hR : ∀ a b, Summable (fun i=> ‖R a b i‖))
    (hS : ∀ a b, Summable (fun i=> ‖U a b i‖)) (hh : ∀ n, R.acts (D n)=U.acts (D n)) : R=U := by
  funext a b x; exact tendsto_nhds_unique (restore_coeff h hR a b x) ((restore_coeff h hS a b x).congr (fun n=>by simp [hh n]))
end tools
lemma must_follow {ι : Type*} {β : Type*} [TopologicalSpace β] {F : Filter ι} [F.IsCountablyGenerated] {f : ι→β} {g : β}
    (h : ∀ k : ℕ→ι, Tendsto k atTop F → ∃ h : ℕ→ℕ, StrictMono h ∧ Tendsto (fun i=> f (k (h i))) atTop (𝓝 g)) : Tendsto f F (𝓝 g) := by
  rw [tendsto_def]; by_contra! he
  obtain ⟨S,hs,hn⟩ := he
  obtain ⟨k,hT,hk⟩ := Filter.frequently_iff_seq_forall.mp (show ∃ᶠ i in F, f i ∉ S from by
     intro hw
     exact hn (by filter_upwards [hw] with i him; simpa using him))
  obtain ⟨m,-,H⟩ := h k hT
  obtain ⟨i,hi⟩ := (H.eventually hs).exists
  exact hk (m i) hi

private lemma approach_mul {α β γ ι : Type*} [Fintype β]
    {U : Filter ι} {a : ι→Matrix α β ℝ} {b : ι→Matrix β γ ℝ} {X : Matrix α β ℝ} {B : Matrix β γ ℝ} (h : Tendsto a U (𝓝 X)) (hh : Tendsto b U (𝓝 B)) : Tendsto (fun i=> a i * b i) U (𝓝 (X*B)) := by
  refine tendsto_pi_nhds.mpr fun x=> tendsto_pi_nhds.mpr fun y=> tendsto_finsetSum _ fun j _ => ?_
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h x) j).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hh j) y)

def pledgeInf (A : Levels G) (m : ℕ) (k l : ℝ) (n : Side) :=
  let X := (blueInf A n k m).map Complex.re
  let d := Exterior.d 2 n
  X + l • ((d * X).transpose * (d * X))

lemma pledge_limit (hk : 0<k) (hl : 0≤l) (n : Side) : Tendsto (fun i=> (pledge k l (location A i m)).acts n) atTop (𝓝 (pledgeInf A m k l n)) := by
  have hY : Tendsto (fun i=> (blue k (location A i m)).acts n) atTop (𝓝 _) := tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=>slate_limit A n hk a b
  have h := approach_mul (tendsto_const_nhds (x:=Exterior.d 2 n)) hY
  have ht := approach_mul (show Tendsto (fun i=>(Exterior.d 2 n * ((blue _ _).acts n)).transpose) atTop (𝓝 ((Exterior.d 2 n * _).transpose)) from tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h b) a) h
  have hc := (hY.add (ht.const_smul l))
  refine hc.congr fun i=>?_
  exact (obligations k l hk hl (A.clock.adm m) _ _).2.1.2.symm

lemma amended (hk : 0<k) (hl : 0 ≤ l) : ∃ Q, Tendsto (fun i=> amend k l (location A i m)) atTop (𝓝 Q) := by
  let f i := amend k l (location A i m)
  obtain ⟨σ,D,hσ,hD,H⟩ := (insurance k l hk hl (A.clock.adm _) (fun i=>location A i m)).1.stock.uniform
  have ht i : (f i).strip σ D := by simpa [f] using H i
  obtain ⟨Q,k1,hk1,hT⟩ := extract_rows (f:=f) fun a b x=>⟨_,fun i=>width_flot (ht i) a b x⟩
  refine ⟨Q,must_follow fun k2' hK => ?_⟩
  obtain ⟨A2,k2,hk2,hT'⟩ := extract_rows (f:=fun i=>f (k2' i)) (fun a b x=>⟨_,fun i=>width_flot (ht _) a b x⟩)
  have hA {w : ℕ→ℕ} {R'} (h : Tendsto (fun i=> f (w i)) atTop (𝓝 R')) (hr : Tendsto w atTop atTop) (n : Side) : (R'.acts n) * pledgeInf A m k l n = 1 := by
    have hx := approach_mul (tendsto_entries h hσ (Eventually.of_forall (fun i=>ht _)) n) ((pledge_limit (m:=m) A hk hl n).comp hr)
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr fun i=> (obligations _ _ hk hl (A.clock.adm _) _ _).2.1.1.symm)
  have hW : Tendsto (fun i=> (⟨i+1,by omega⟩ : Side).val) atTop atTop := tendsto_atTop_mono (fun i : ℕ=> show id i ≤ _ from Nat.le_succ i) tendsto_id
  have hZ {w : ℕ→ℕ} {X} (h : Tendsto (fun i=> f (w i)) atTop (𝓝 X)) a b : Summable fun z=> ‖X a b z‖ := (flot_summable hσ (D:=D)).of_nonneg_of_le (fun _=>norm_nonneg _) (fun z=> by
     have h0 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h a) b) z; apply le_of_tendsto h0.norm; exact Eventually.of_forall fun i=> width_flot (ht _) _ _ _)
  suffices htEq : A2 = Q by exact ⟨k2,hk2,htEq ▸ hT'⟩
  refine restore_rows hW (hZ hT') (hZ hT) ?_
  intro n
  let X := Q.acts (⟨n+1,by omega⟩:Side); let Z := A2.acts (⟨n+1,by omega⟩:Side); let P := pledgeInf A m k l ⟨n+1,by omega⟩
  have hk := hA hT' (hK.comp hk2.tendsto_atTop) (⟨n+1,by omega⟩:Side)
  have hv := mul_eq_one_comm.mp (hA hT hk1.tendsto_atTop (⟨n+1,by omega⟩:Side))
  change Z = X
  calc
    Z = Z * (P * X) := by rw [show P*X=1 from hv,mul_one]
    _ = Z * P * X := by rw [mul_assoc]
    _ = X := by rw [show Z*P=1 from hk,one_mul]

end YM.Next.Free.UV

import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.ChipHeal
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.Progress.STATIONARY_SCENES.Frames
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bed

/-!
# Spend at uncut tail and zero; not mutating the Tube

And obtain residue pricing on one addressed row, regardless of
branch/frozen data. The factors of color/channel booking inserted in
the Consumers after returning to actual data. Need two flat metric
provenances. All genuine at order zero. Does not require all stores to
be realizable or usable-ing assumption on the cover stencil--only the
sec sector resources and flags exactly stated, no \'post\' datum from
a different horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Lift
open Function Filter Lattice RG Wilson Finset Pressure Pressure.Stores Pressure.Tube Precision Exterior Tree Bloch Bid Matrix
open Next Next.Fluctuations SectorChange SectorChange.Rows SectorChange.Gaussian Push.SectorMeasure  Remote Oriented
open scoped Topology InnerProductSpace BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x t : ℝ}

lemma ideal_tail (G : Gauge) (P : Patch) {E σ : ℝ} (he : 0≤E) : ∃ C : ℝ, 0≤C ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → ∀ Λ, T.up.Bounds T.high σ E Λ → ∀ (x : ℝ) (a : Directions G f) (i : Slots S),
    ‖Flat.omitted T x a i‖ ≤ C*‖a‖*Real.exp (-σ*(till x)) := by
  obtain ⟨C,hC,hf⟩ := LocalJet.face_global G
  let B : ℝ := Fintype.card (Site P.L)*(LocalJet.grain 1*Fintype.card Axis); have hb : 0≤B := by unfold B LocalJet.grain; positivity
  refine ⟨E*C*B,by positivity,?_⟩
  intro c f S T hp Λ hT x a i
  rcases i with ⟨s,j|b⟩; swap
  · change ‖(0:G.Color)‖ ≤ _; rw [norm_zero]; positivity
  unfold Flat.omitted; simp only [Sum.elim_inl]; split
  swap; rw [norm_zero]; positivity
  let k l:= (T.up.row j.1.2 l).1; let p l := (T.up.row j.1.2 l).2
  let R:=till x; let v (i : Cell f):=Work.F03.faceCurl i (pulled (Flat.labels a) s)
  let H (l : ℕ) := if R<(p l).length then k l • v (Work.F03.slotFace (p l) j.1.1) else 0
  let q (l : ℕ) := |k l| * Real.exp (σ*(p l).length)
  have hq : SumBudget q E := hT.rows _
  let D:=C*B*‖a‖; have hD : 0≤D := by unfold D; positivity
  have hh (l) : ‖H l‖ ≤ q l * (D*Real.exp (-σ*R)) := by
    unfold H; split
    next h =>
      let i:=Work.F03.slotFace (p l) j.1.1
      rw [norm_smul,Real.norm_eq_abs]
      change |k l| * ‖v i‖ ≤ _
      rw [show v i=plaquetteJet S (1:Config G c) s i a from (Flat.flat_curl ..).symm,plaquetteJet,(Motion.plaquette_turn _ _ _ (LocalJet.face_smooth ..).contDiffAt).2]
      refine (mul_le_mul_of_nonneg_left (hf S i _ _) (abs_nonneg _)).trans ?_
      have hb' : LocalJet.settle S (S.ratio.parent i.1) 1 (Motion.inChannel s (replica S.ratio 1) a) ≤ B*‖a‖ := by
        have hb' : LocalJet.chips S 1 = B := by simp [LocalJet.chips,B,hp]
        rw [← hb']; apply SourceBill.settles _ _ _ _ (norm_nonneg _)
        intro l; rw [Motion.in_size]; exact norm_le_pi_norm a _
      have hs : 1 ≤ Real.exp (σ * (p l).length) * Real.exp (-σ*R) := by
        rw [← Real.exp_add]; apply Real.one_le_exp
        have hi : (R:ℝ)≤(p l).length := by exact_mod_cast h.le
        have hz:=hT.width; nlinarith
      unfold q
      calc
        _ ≤ |k l| * D := by unfold D; rw [mul_assoc C]; gcongr
        _ ≤ _ := by have hi := le_mul_of_one_le_right hD hs; calc
                     _ ≤ |k l| * (D*(Real.exp (σ*(p l).length)*Real.exp (-σ*R))) := mul_le_mul_of_nonneg_left hi (abs_nonneg _)
                     _ = _ := by ring
    rw [norm_zero]; apply mul_nonneg (hq.1 _); positivity
  let u := D*Real.exp (-σ*R); have ht := hq.2.1.mul_right u
  have hs := Summable.of_nonneg_of_le (fun i=>norm_nonneg (H i)) hh ht
  change ‖∑' i,H i‖ ≤ _
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hh ht).trans ?_)
  rw [tsum_mul_right]
  apply (mul_le_mul_of_nonneg_right hq.2.2 (show 0 ≤ u from mul_nonneg hD (Real.exp_pos _).le)).trans_eq
  unfold u D R; ring

-- retain pricing of perturbation proportional to vector norm
lemma pulse_cost (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (C : ℝ) (hp : P.Branches K G) (hC : 0 ≤ C) :
    ∃ A δ : ℝ, 0≤A ∧ 0<δ ∧ ∀ t : ℝ, 0≤t → t ≤ δ → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (T : Tube G S) (Λ σ : ℝ), T.high=p → T.up.Bounds p σ C Λ → ∀ (x : ℝ) (o : Site c) (D : ℕ) (V : Config G c),
    paid S (replica S.ratio V) o D t → ∀ (a : Directions G f), invoice S a o D →
    ∀ (k:S.Choices) (i : Slots S), separation o (Remote.aim S i)+SectorChange.span P x ≤ D →
      ‖bump T x V k a i-bump T x (1:Config G c) k a i‖ ≤ A*(1+(till x:ℕ))*t*‖a‖ := by
  obtain ⟨A,δ,hA,hδ,h⟩ := pulse_bill G P K p C hp hC
  refine ⟨A,δ,hA,hδ,?_⟩; intro t ht he c f S Hs hK T Λ σ hh hx x o D V hV a ha k i HS
  by_cases hu : a=0
  · rw [hu,norm_zero,mul_zero,show (0: Directions G _)=(0:ℝ) • a from (zero_smul ..).symm, bump_smul T x V k hx, bump_smul T x (1:Config G c) k hx,zero_smul,zero_smul,sub_self,norm_zero]
  let z:=‖a‖⁻¹
  have hz : 0 < ‖a‖ := norm_pos_iff.mpr hu
  have hL : ‖z • a‖ ≤ 1 := by rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hz).le,inv_mul_cancel₀ hz.ne']
  obtain ⟨hs,-⟩ := h t ht he S Hs hK T _ σ hh hx x o D V hV (z • a) hL (fun e h => by rw [Pi.smul_apply,ha e h,smul_zero]) k i HS
  simp_rw [bump_smul T x _ k hx,Pi.smul_apply, ← smul_sub,norm_smul,z,Real.norm_of_nonneg (inv_pos.mpr hz).le, inv_mul_eq_div] at hs
  exact (div_le_iff₀ hz).mp hs

def peon (a : Directions G f) (o : Site c) (R : ℕ) : Directions G f := fun i => if separation o (S.ratio.parent i.1) ≤ R then a i else 0
lemma peon_nn (a : Directions G f) (o : Site c) (R : ℕ) : ‖peon (S:=S) a o R‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; unfold peon; split
  · exact norm_le_pi_norm a _
  rw [norm_zero]; positivity

def marked (U : Stores S) (x : ℝ) (F : Forest S.ratio) (a : Directions G f) : Prices G (SectorChange.Active U x F) :=
  tape.symm fun i => a i.val.val

theorem prepared (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (C σ : ℝ) (hp : P.Branches K G) (hC : 0 ≤ C) (_hs : 0<σ) :
    ∃ A δ : ℝ, 0≤A ∧ 0<δ ∧ ∀ t : ℝ, 0≤t → t ≤ δ → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (T : Tube G S) Λ, T.high=p → T.up.Bounds p σ C Λ → ∀ (U : Stores S) (F : Forest S.ratio) (x : ℝ) (o : Site c)
      (D : ℕ) (V : Config G c), paid S (replica S.ratio V) o D t → Clears U x o D →
    ∀ (k:S.Choices) (i : Slots S), separation o (Remote.aim S i)+SectorChange.span P x ≤ D →
      (∀ a : Directions G f, (∀ i∈F.trunks, a i=0) →
          ‖(bump T x V k (fresh x (shots S x) U F (tape (marked U x F a)))) i-Flat.ideal T a i‖ ≤ A*‖a‖*(widen (till x) t σ)) ∧
      ∀ y : LogArray G (Frozen U x F), bump T x V k (input x U F y) i=0 := by
  obtain ⟨B,δ,hB,hδ,hh⟩ := pulse_cost G P K p C hp hC
  obtain ⟨Y,hY,hy⟩ := ideal_tail (σ:=σ) G P hC
  refine ⟨B+Y,δ,add_nonneg hB hY,hδ,?_⟩
  intro t ht he c f S hP hK T Λ hv hT U F x o D V hx hU k i H0
  have hB' : S.patch.Branches S.kernel G := by rw [hP,hK]; exact hp
  have hl (e : Bond f) (he : e ∈ shots S x i.1 (i.2.elim (fun x => .inl x.1) Sum.inr)) : separation o (S.ratio.parent e.1) ≤ D := by
    have h := (contains ..).mp he
    rw [← hP] at H0
    exact (separation_triangle o (Remote.aim S i) _).trans ((Nat.add_le_add_left h _).trans H0)
  have H (a b : Directions G f) (h : ∀ e : Bond f, separation o (S.ratio.parent e.1)≤ D → a e=b e) : bump T x V k a i= bump T x V k b i := bump_dep T x V k i.1 i.2 a b hB' (fun e hv => h e (hl e hv))
  constructor
  · intro a h
    let v:=peon (S:=S) a o D
    let X:=fresh x (shots S x) U F (tape (marked U x F a))
    have hV : invoice S v o D:= fun i h=> if_neg h
    have hv' : ‖v‖ ≤ ‖a‖:=peon_nn a o D
    rw [show bump T x V k X i=bump T x V k v i from H X v (by
      intro e he
      unfold X v peon marked
      rw [if_pos he,MeasurableEquiv.apply_symm_apply]
      unfold fresh; split
      · rename_i hi; have hw := live_test U F hU (⟨e,hi⟩:F.Free) he; rw [dif_pos hw]
      · rename_i hi; exact (h e (not_not.mp hi)).symm)]
    obtain hl' := hh t ht he S hP hK T Λ σ hv hT x o D V hx v hV k i H0
    rw [← hv] at hT
    rw [bump_dep T x (1:Config G c) k i.1 i.2 v a hB' (fun j h=>if_pos (hl _ h))] at hl'
    let R:=till x
    let w:=Flat.omitted T x a i
    have hY0 : Flat.ideal T a i=bump T x (1:Config G c) k a i+w := congr_fun (Flat.ideal_checks T k hT hB' x a) i
    rw [hY0,← sub_sub]
    have hZ := Real.exp_pos (-σ * (R:ℝ))
    have hn := norm_nonneg a
    apply (norm_sub_le ..).trans ((add_le_add hl' (hy S T hP Λ hT x a i)).trans ?_)
    let r := (1+(R:ℝ)); have hr : 0 ≤ r := by unfold r; positivity
    calc
      _ ≤ B*r*t*‖a‖ + Y*‖a‖*Real.exp (-σ*R) := add_le_add_left (mul_le_mul_of_nonneg_left hv' (by have hvB : 0≤B := ‹_›; positivity)) _
      _ ≤ _ := by
        unfold widen r R at *
        nlinarith only [hZ, mul_nonneg hY (show 0≤‖a‖*((1+(till x:ℝ))*t) from mul_nonneg hn (by positivity)),
          mul_nonneg (show 0≤B from ‹_›) (show 0≤‖a‖*Real.exp (-σ*↑(till x)) from mul_nonneg hn hZ.le)]
  intro y
  rw [H (input x U F y) 0 (by
    intro e he; unfold input; split
    next hi => have hw := live_test U F hU (⟨e,hi⟩:F.Free) he; rw [dif_neg hw]; rfl
    rfl),show (0:Directions G f)=(0:ℝ) • (0:Directions G f) from (zero_smul ..).symm,bump_smul T _ _ _ hT, zero_smul]; rfl
end YM.AnalyticBridge.LocalGaussianLaws.Lift

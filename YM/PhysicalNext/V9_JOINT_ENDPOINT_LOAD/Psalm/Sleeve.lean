import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Seat
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pool

/-! # Central-guard prices with projection strictly within a requested
sub-stencil of the actual unforced operand. Eventually-vanishing tests
will refer to these exact fields, not a cutoff of Z on halo positions
that weren't in the parent h. No regular projection Y -> U assumed except
`Museum` covering these uses (test every such link even when discarding). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Planned.AtomRegular.Foliage AnalyticBridge.LocalGaussianLaws Heir
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {I : Type} [Fintype I]
    {X : Support f} {Y : Support c} {P B : BudgetPoint} {Pt : Teller G} {n : ℕ} {x u t : ℝ} {q : Chi} {d : ℝ} {V W : Config G c}
    {o p : Site c} {g : Site c → G.El} {C : Libretto G n} {D : Record}

abbrev Needs {f : Side} (Z : Set (Site f)) (e : Bond f) := e.1∈ Z ∧ e.1+step e.2∈ Z

def Guarded (a : Museum F x A X Y I) (Z : Set (Site f)) (u t : ℝ) (z : Prices G I) := ∀ i, Needs Z (a.address i) → u*‖tape z i‖ ≤ t

def trimmed (a : Museum F x A X Y I) (Z : Set (Site f)) (z : Prices G I) : Prices G I := fun i => if Needs Z (a.address i.1) then z i else 0

variable (a : Museum F x A X Y I) {E : Set (Site f)} (U : Config G c → Config G f) (w : Config G c → Prices G I)
    {i : I} {z : Prices G I} {e : Bond f}
private lemma trim_price (hu : 0 < u) (ht : 0 ≤ t) (hg : Guarded a E u t z) : u*‖tape (trimmed a E z)‖ ≤ t := by
  rw [mul_comm u,← le_div_iff₀ hu]; apply (pi_norm_le_iff_of_nonneg (div_nonneg ht hu.le)).mpr; intro i
  by_cases hi : Needs E (a.address i)
  · rw [show tape (trimmed a E z) i=tape z i by ext j; exact if_pos hi]; exact (le_div_iff₀ hu).mpr ((mul_comm ..).trans_le (hg i hi))
  rw [show tape (trimmed a E z) i=0 by ext j; exact if_neg hi,norm_zero]; positivity

lemma credited (i : I) (z : Prices G I) (y : Config G f) : a.deposited k T q d u W y z (a.seat i) = vocal T x k A F q d y W (a.seat i) + u • tape z i := by
  rw [Museum.deposited, a.seat.injective.extend_apply]

abbrev replay (T : Tube G S) (x : ℝ) (k : S.Choices) (q : Chi) (d u : ℝ) {A : Stores S} {F : Forest S.ratio} (a : Museum F x A X Y I)
    (U : Config G c → Config G f) (w : Config G c → Prices G I) (W : Config G c) (e : Bond f) :=
  if Needs (inspected X) e then a.received k T q d u W (U W) (w W) e else 1

lemma replay_agrees : Agrees (inspected X) (a.received k T q d u W (U W) (w W)) (replay T x k q d u a U w W) := fun _ h h' => (if_pos ⟨h,h'⟩).symm

lemma station_release {W : Config G c} (hi : a.address i = e) : a.received k T q d u W (U W) z e = G.lieExp (a.deposited k T q d u W (U W) z (a.seat i)) * replica S.ratio W e := by
  subst e; unfold Museum.received physical SectorChange.returned thaw; change F.drape _ (a.seat i).val.val=_; rw [F.off_tree,freeze_regular]; rfl

lemma trim_same (he : E⊆inspected X) : Agrees E (a.received k T q d u W (U W) z) (a.received k T q d u W (U W) (trimmed a E z)) := by
  intro e hi hj; by_cases ht : e∈F.trunks
  · exact (F.on_tree _ ⟨e,ht⟩).trans (F.on_tree _ ⟨e,ht⟩).symm
  let s : Active A x F := ⟨⟨e,ht⟩, a.admits (he hi) (he hj)⟩
  obtain ⟨j,hj'⟩ := a.covers s (he hi) (he hj)
  have h : a.address j=e := congr_arg (fun i : Active A x F => i.val.val) hj'
  rw [station_release a U h,station_release a U h, credited a,credited a]
  rw [show tape (trimmed a E z) j=tape z j by ext i; exact if_pos (h.symm ▸ ⟨hi,hj⟩)]

variable (h : Plays C D P B Pt T x) (hV : Healthy P.threshold Y V)
include h hV
lemma inspected_toll (e : Cell f) (ht : Tests X e) (hu : 0 < u) (hg : Guarded a (touched e) u (D.ε*B.threshold) z) :
    G.chord (faceValue (a.received k T q d u V (U V) z) e) < B.threshold/8 := by
  let Y : Set (Site f) := touched e; let y := trimmed a Y z; have he := D.guards
  have hv := strict (k:=k) (q:=q) (d:=d) h.sew C.width C.price h.rehearsed.early (h.acts F k) D.majorant
    (by have := h.rehearsed.test; have := P.order_ge; omega) h.rehearsed.tensions a h.bulletin C.Z rfl h.rehearsed.wire h.space h.rehearsed.temp_eq hV (U V) y hu.le
    (trim_price a hu (mul_nonneg he.le B.threshold_pos.le) hg) B.threshold_pos e ht
  suffices H : faceValue (a.received k T q d u V (U V) z) e = faceValue (a.received k T q d u V (U V) y) e by rwa [H]
  exact travel_local _ _ _ _ fun i hi hj => trim_same a U (E:=Y) ht.retain i (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hj)

def storeCost (C : Libretto G n) := voiceCost C+1
omit h hV in
lemma storeCost_pos (C : Libretto G n) : 0 < storeCost C := add_pos (zero_lt_one.trans_le (voiceCost_one ..)) zero_lt_one

lemma displacement (hu : 0 ≤ u) (i : I) (hz : u * ‖tape z i‖ ≤ D.ε*B.threshold) : ‖a.deposited k T q d u V (U V) z (a.seat i)‖ ≤ storeCost C * B.threshold := by
  rw [credited a]; refine (norm_add_le ..).trans ?_
  rw [norm_smul_of_nonneg hu]; have hh := vocal_bound (q:=q) (d:=d) (k:=k) h a hV (a.seat i) ((Corona.halo_mono (by omega : Heir.reach x + 1 ≤ Heir.reach x + 4) (Finset.Subset.refl _)).trans (a.stores i)) (U V)
  have hε := h.rehearsed.tensions.narrow.trans (by norm_num : (1/128:ℝ) ≤ 1)
  unfold storeCost; rw [add_mul,one_mul]; exact add_le_add hh (hz.trans (mul_le_of_le_one_left B.threshold_pos.le ((le_mul_of_one_le_left D.guards.le C.web.cost).trans hε)))

lemma deposit_cont (hw : ContinuousAt w V) (i : I) : ContinuousAt (fun W => a.deposited k T q d u W (U W) (w W) (a.seat i)) V := by
  simp_rw [credited a]; refine (vocal_cont h a hV (a.seat i) ((Corona.halo_mono (by omega : Heir.reach x + 1 ≤ Heir.reach x + 4) (Finset.Subset.refl _)).trans (a.stores i)) U).add ?_
  exact ((continuous_apply i).continuousAt.comp (gaugeCount.continuous.continuousAt.comp hw)).const_smul u

lemma replay_cont (hw : ContinuousAt w V) : ContinuousAt (replay T x k q d u a U w) V := continuousAt_pi.mpr fun i => by
  unfold replay; split; swap; exact continuousAt_const
  next hi =>
  by_cases ht : i∈F.trunks
  · have hh W : a.received k T q d u W (U W) (w W) i=1 := F.on_tree _ ⟨i,ht⟩
    simp_rw [hh]; exact continuousAt_const
  let s : Active A x F := ⟨⟨i,ht⟩,a.admits hi.1 hi.2⟩
  obtain ⟨j,hj⟩ := a.covers s hi.1 hi.2; have hj : a.address j=i := congr_arg (fun z : Active A x F => z.val.val) hj
  simp_rw [station_release a U hj]
  apply (G.lieExp_cont.continuousAt.comp (deposit_cont a U w h hV hw j)).mul
  unfold replica; split; exact continuousAt_const; exact (continuous_apply _).continuousAt
end YM.PhysicalNext.JointLoad.Psalm

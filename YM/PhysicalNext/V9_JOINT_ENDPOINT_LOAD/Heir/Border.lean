import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Depth
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Duet
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Shelter
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Tickets

/-! # Strict guard on actual inherited E reads and all incident faces

Tree links restored in one and same gauge per buffer. Guard support
on ALL requested marginal elements; profile and telescopic/suppression
uses (companion and others in the full alphabet) are SEPARATE issues,
not dismissing their tests of the broad chart radius by this theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Tree Next Next.SectorChange Next.SectorChange.Rows Wisps
    Precision Next.Fluctuations Exterior Bloch Bid AnalyticBridge.LocalGaussianLaws Push.SectorMeasure Matrix
    Planned.AtomRegular.Foliage
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {k : S.Choices} {F : Forest S.ratio} {A : Stores S} {o : Site c}
    {I : Type} {Pt : Teller G} {P B : BudgetPoint} {X : Support f} {Y : Support c} {V : Config G c}
    {r Q C M ε δ x v t : ℝ} {W : Web G} {q : Chi} {d u : ℝ} {n : ℕ}

/-- Purely numerical conditions. Caller knows at most the two stages and L,
then pays heights before inspecting any actual fields or occurrence data. -/
structure Tension (W : Web G) (δ Q ε x r v t : ℝ) : Prop where
  coarse : temp x ≤ 2*t
  allows : v < r
  small : Q*v ≤ min W.radius 1
  quartic : W.scale*(Q*(temp x+v))^2 ≤ t/128
  decay : W.scale*v ≤ 3*t*Real.exp (δ*radiusB x)
  noise : ε*t ≤ v
  narrow : W.scale*ε ≤ 1/128

def licensed (δ M : ℝ) (L : Side) := yarn δ M ≤ (L.val:ℝ)^2/128

lemma face_sub_bound (W : Web G) (i : Cell f) {a b : Directions G f} : ‖Work.F03.faceCurl i (Flat.labels a)‖ ≤ ‖Work.F03.faceCurl i (Flat.labels b)‖ + W.scale*‖a-b‖ := by
  let h (a : Directions G f) := Work.F03.faceCurl i (Flat.labels a)
  have ht : h a-h b=h (a-b) := by
    unfold h Work.F03.faceCurl; ext j; exact (congr_fun (Matrix.mulVec_sub (Exterior.d 1 f) (parts G 1 (Flat.labels a) j) (parts G 1 (Flat.labels b) j)) (i.1, plaquette i.2)).symm
  calc
    ‖h a‖ ≤ ‖h b‖+‖h a-h b‖ := by simpa using norm_add_le (h b) (h a-h b)
    _ ≤ _ := by rw [ht]; exact add_le_add_right ((W.linear _ i).trans (mul_le_mul_of_nonneg_left (labels_area _) (zero_le_one.trans W.cost))) _

def Tests (X : Support f) (i : Cell f) := ∃ j∈X,j∈touched i
lemma Tests.retain {i : Cell f} (ht : Tests X i) : touched i ⊆ inspected X := by
  intro y hy; apply Finset.mem_union_right; apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩; rw [if_neg (Finset.not_disjoint_iff.mpr ht)]; exact hy

lemma Museum.canvas (a : Museum F x A X Y I) (i : Site f) (he : i∈ inspected X) (hB : Healthy P.threshold Y V) (hr : 100*(1+radiusB x)≤c.val)
    (Z : Collar G n) (hn : 1 ≤ n) (hz : Cube.Wire P (reach x) Z) : ∃ g, Canvas P (S.ratio.parent i) (reach x) V g n (Cube.fee Z) :=
  primed hB ((Corona.halo_mono (Nat.add_le_add_left (show 1≤4 by norm_num) _) (Finset.Subset.refl _)).trans (a.asks i he)) (roomy hr) Z hn hz

lemma display_price (h : Act T F x k n r Q) (hn : 1 ≤ n) {p : Deck G c f} (ha : ‖p‖ ≤ v) (hr : v ≤ r) (hQ : 1≤Q) : ‖display T F x k true p‖ ≤ Q*v :=
    (locate (h.costs true).uniform hn (h.costs true).home (ha.trans hr)).trans (mul_le_mul_of_nonneg_left ha (zero_le_one.trans hQ))

section protection
variable (s : Seam T δ M) (hd : 0<δ) (hm : 0≤M) (hL : licensed δ M S.patch.L)
    (hT : Act T F x k n r Q) (hQ : 1≤Q) (hn : 2 ≤ n) (hc : Tension W δ Q ε x r v t)
include s hd hm hL hT hQ hn hc
set_option maxHeartbeats 700000 in
lemma border_toll (ht : 0<t) (i : Cell f) (h : Museum.Station Y x (S.ratio.parent i.1))
    {g : Site c → G.El} {p : Deck G c f} (ha : ‖p.1‖ ≤ v) (hz : ‖p.2‖ ≤ ε*t)
    (hV : Healthy (temp x) Y V) (he : AgreeNear id (S.ratio.parent i.1) (reach x) (gauge g V) (increment 1 p.1)) :
    G.chord (faceValue (sounds T F x k true p) i) < t/8 := by
  let R := display T F x k true; let y := route T p.1; have hW := W.cost
  have hp : ‖p‖ ≤ v := max_le ha (hz.trans hc.noise)
  have hv := (norm_nonneg p).trans hp
  have he₁ : v ≤ Q*v := le_mul_of_one_le_left hv hQ
  have he₂ := hc.small.trans (min_le_left ..)
  have he₃ := display_price hT (by omega) hp hc.allows.le hQ
  have h0 := Work.E04.temp_nonneg x
  have hQa : v ≤ Q*(temp x + v) := he₁.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h0) (by positivity))
  have hK : W.scale*(Q*(temp x+v)*v) ≤ t/128 := le_trans (by gcongr ?_*?_; rw [sq]; gcongr) hc.quartic
  have hb : W.scale*‖Flat.labels (R p)‖^2 ≤ t/128 := le_trans (by
    gcongr; apply ((labels_area _).trans he₃).trans; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h0) (by positivity)) hc.quartic
  have hu := s.shield hd hm W hV h he hc.coarse ha (he₁.trans he₂) ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hQa _) (by positivity)).trans (hc.quartic.trans (by linarith))) hc.decay i rfl
  have hu : ‖Work.F03.faceCurl i (Flat.labels y)‖ ≤ t/128 := hu.trans ((div_le_iff₀ (by positivity)).mpr (by unfold licensed at hL; nlinarith only [mul_le_mul_of_nonneg_right hL ht.le]))
  have hq : ‖R p-y‖ ≤ Q*(temp x+v)*v+ε*t := by
    have h := (hT.costs true).zeroth_charge hn hp hc.allows.le
    change ‖R p-(y+p.2)‖ ≤ _ at h
    exact (by simpa [sub_add_eq_sub_sub] using (norm_add_le (R p-(y+p.2)) p.2).trans (add_le_add h hz))
  have hh := face_sub_bound (b:=y) (a:=R p) W i
  have hr' := ((labels_area _).trans he₃).trans he₂
  let a := Flat.labels (R p)
  let b := G.curvature (faceValue (represent a) i); let f := Work.F03.faceCurl i a
  have hf : ‖f‖ ≤ t/128+t/128+t/128 := le_trans hh (by
    have h := mul_le_mul_of_nonneg_left hq (zero_le_one.trans hW); have he := mul_le_mul_of_nonneg_right hc.narrow ht.le; nlinarith only [h,hu,hK,he])
  have hc' : ‖b‖ ≤ t/32 := le_trans (norm_le _ _ (le_trans (W.defect _ i hr') hb) hf) (by linarith)
  rw [← hT.represents true p (hp.trans hc.allows.le), ← labels_eq]
  apply (W.travel _ i hr').trans_lt; change 2*‖b‖ < _; linarith
where norm_le (b f : G.Color) {u v : ℝ} (h : ‖b-f‖ ≤ u) (hh : ‖f‖ ≤ v) : ‖b‖ ≤ u+v := by simpa using (norm_add_le (b-f) f).trans (add_le_add h hh)
variable (a : Museum F x A X Y I) [Fintype I] (b : Folio.Bulletin x Pt T)
    (Z : Collar G n) (ha : v=loom P (reach x) (Cube.fee Z)) (hz : Cube.Wire P (reach x) Z) (hF : 100*(1+radiusB x)≤c.val) (hr : P.threshold=temp x)
    (hV : Healthy P.threshold Y V) (U : Config G f) (w : Prices G I) (hu : 0≤u) (he : u*‖tape w‖ ≤ ε*t)
include b Z ha hz hF hr hV hu he
lemma strict (ht : 0<t) (p : Cell f) (h : Tests X p) : G.chord (faceValue (a.received k T q d u V U w) p)<t/8 := by
  letI := Classical.decEq I
  let o := S.ratio.parent p.1
  obtain ⟨g,hg⟩ := a.canvas p.1 (h.retain (Work.E01.base_touched p)) hV hF Z (by omega) hz
  let y := crop o (reach x) g V
  let z := a.extra g u w
  have h₀ := ((Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (a.asks _ (h.retain (Work.E01.base_touched p))) : Museum.Station Y x o)
  have hy : AgreeNear id o (reach x) (gauge g V) (increment 1 y) := hg.seen.self_of_nhds
  have hp := border_toll s hd hm hL hT hQ hn hc (p:=(y,z)) ht p h₀ (ha.symm ▸ hg.paid (Cube.fee_one ..)) ((a.extra_size g u hu w).trans he) (hr ▸ hV) hy
  have hf : faceValue (sounds T F x k true (y,z)) p=faceValue (gauge (fun i => G.lieExp (φ T F true y i)) (gauge (g ∘ S.ratio.parent) (a.received k T q d u V U w))) p := by
    refine travel_local _ _ _ _ (fun i hi hj => a.heard g u b (h.retain (List.mem_toFinset.mpr hi)) (h.retain (List.mem_toFinset.mpr hj)) h₀ ?_ _ w U hy)
    apply (Work.E04.parent_separation ..).trans; have h := Work.E01.sep_touched p i.1 (List.mem_toFinset.mpr hi); omega
  rwa [hf,face_gauge,G.chord_conj,face_gauge,G.chord_conj] at hp
lemma border_healthy (ht : 0<t) : Healthy t X (a.received k T q d u V U w) := Finset.disjoint_left.mpr (by
  intro i hi hj; obtain ⟨p,hp,h⟩ := (flags_spec ..).mp hj; have hg := (strict (d:=d) (q:=q) s hd hm hL hT hQ hn hc a b Z ha hz hF hr hV U w hu he ht p ⟨i,hi,hp⟩); linarith)
end protection
end YM.PhysicalNext.JointLoad.Heir

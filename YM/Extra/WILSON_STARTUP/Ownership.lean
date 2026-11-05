import YM.Extra.WILSON_STARTUP.Design
import YM.Work.B04
import YM.Work.H03

/-!
# One-row startup energy and locality

Charge all
remaining differences (nonnegative, also for small r_p with flag nearby or
where the soft kept-row test fails) to compulsory packets, at the **actual
signed-channel** locations. There are NO logarithm attachments in this plan.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup
open Function Filter Tensor RG Wilson Lattice Design Work
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} (c : Clip) (b : BudgetPoint)

structure Decent : Prop where
  direct : c.direct ≤ 1
  radius : 2 ≤ b.B
  cut : 2 ≤ b.threshold * Real.exp (((b.B - 2 : ℕ):ℝ) / c.relaxation)

theorem too_far (h : Decent c b) (V : Config G n) (p : Cell n) (x : Site n)
    (hh : b.B-2 ≤ separation x p.1) :
    G.chord (faceValue V p) ≤ b.threshold*Real.exp (separation x p.1 / c.relaxation) := by
  apply (G.chord_le_two _).trans (h.cut.trans ?_)
  have := b.threshold_pos; have := c.radius_pos
  gcongr

theorem kept_small (U : Config G n) (p : Cell n) (h : PathData.kept c b.threshold p.1 U) :
    G.chord (faceValue U p) ≤ b.threshold := by simpa using h p

-- First in any one orientation channel's coordinates
def due (U : Config G n) (p : Cell n) :=
    let u := faceValue U p; let r := G.chord u; let k := bulk c * ‖G.curvature u‖^2/2
    if b.threshold < r then G.price u - c.linear * b.threshold * r
    else (if Healthy b.threshold (touched p) U then k else bulk c * G.price u) -
        (if PathData.kept c b.threshold p.1 U then k else 0)

lemma due_large (hc : c.direct ≤ 1) (U : Config G n) (p : Cell n)
    (ht : b.threshold < G.chord (faceValue U p)) : b.threshold^2/4 ≤ due c b U p := by
  let r := G.chord (faceValue U p)
  have hb := b.threshold_pos
  have hl : c.linear ≤ 1/4 := by have := c.kink; linarith
  unfold due; rw [if_pos ht]
  have he : c.linear*b.threshold*r ≤ (1/4)*r*r := by dsimp only [r]; gcongr; exact G.chord_nonneg _
  nlinarith [G.chord_price (faceValue U p)]

lemma due_range (hc : c.direct ≤ 1) (U : Config G n) (p : Cell n) : due c b U p ∈ Set.Icc (0:ℝ) 2 := by
  let u := faceValue U p
  have ht := b.threshold_pos; have hr := G.chord_nonneg u; have hl := c.tail_pos
  have hd : 0 ≤ bulk c := sub_nonneg.mpr hc
  have he : bulk c * ‖G.curvature u‖^2 / 2 ≤ bulk c * G.price u := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm u) 2) hd, G.chord_price u]
  have hf := G.price_range u
  have hp : bulk c * G.price u ≤ 2 := by
    unfold bulk; nlinarith [c.quadratic_pos,hf.1,hf.2]
  have hk : 0 ≤ bulk c * ‖G.curvature u‖^2 / 2 := by positivity
  by_cases h : b.threshold < G.chord u
  · exact ⟨(by positivity : (0:ℝ) ≤ b.threshold^2/4).trans (due_large c b hc U p h), by
      unfold due; rw [if_pos h]; exact (sub_le_self _ (by change 0 ≤ _ * G.chord u; positivity)).trans hf.2⟩
  unfold due; rw [if_neg h]
  change (if Healthy _ _ _ then bulk c * ‖G.curvature u‖^2/2 else bulk c*G.price u) - _ ∈ _
  split_ifs <;> constructor <;> linarith

lemma due_eq (hc : c.direct ≤ 1) (U : Config G n) (p : Cell n) :
    G.price (faceValue U p) = (top G c).baseTerm c b U p + masked b.threshold (touched p)
      (fun V => diagonal (panel G c) (G.curvature (faceValue V p))) U +
        bulk c * masked b.threshold (touched p) (residual G p) U + due c b U p := by
  unfold PathData.baseTerm PathData.clipped due; dsimp only
  rw [ell_sq _ hc,G.chord_price]
  by_cases hh : Healthy b.threshold (touched p) U
  · have he := healthy_chord p U hh
    rw [if_pos he,if_neg (not_lt.mpr he),if_pos hh,masked_eq _ _ _ _ hh,masked_eq _ _ _ _ hh]
    simp only [panel,diagonal,smul_apply,smul_eq_mul,residual,surplus,bulk]; ring
  rw [masked_ne _ _ _ _ hh,masked_ne _ _ _ _ hh,if_neg hh]
  by_cases he : b.threshold < G.chord (faceValue U p)
  · rw [if_pos he,if_neg (not_le.mpr he),if_neg (fun h => not_le.mpr he (kept_small c b U p h))]; ring
  rw [if_neg he,if_pos (le_of_not_gt he)]; unfold bulk; ring

lemma due_gauge (U : Config G n) (k : Site n → G.El) (p : Cell n) : due c b (gauge k U) p = due c b U p := by
  simp only [due,face_gauge,G.chord_conj,G.price_conj,Healthy,gauge_flags,
    PathData.kept,G.curvature_conjugate,G.norm_adjoint]
  congr!

lemma due_measurable (p : Cell n) : Measurable fun U : Config G n => due c b U p := by
  unfold due; refine Measurable.ite (isOpen_lt continuous_const (by unfold faceValue; fun_prop)).measurableSet
    (by unfold faceValue; fun_prop) (Measurable.sub ?_ ?_)
  · exact Measurable.ite (healthy_closed .. |>.measurableSet) (by unfold faceValue; fun_prop) (by unfold faceValue; fun_prop)
  exact Measurable.ite (PathData.kept_closed .. |>.measurableSet) (by unfold faceValue; fun_prop) measurable_const

lemma aff_inj (s : Signed) (x : Site n) : Injective (affine s x) := fun _ _ h => s.act_injective (add_right_cancel h)

def frameSites (s : Signed) (x : Site n) : Equiv.Perm (Site n) := Equiv.ofBijective (affine s x)
  ⟨aff_inj ..,Finite.injective_iff_surjective.mp (aff_inj ..)⟩

lemma pulls_gauge (s : Signed) (x : Site n) (U : Config G n) (k : Site n → G.El) :
    pull s x (gauge k U) = gauge (k ∘ affine s x) (pull s x U) := by
  funext i; change ((posDir i.2).rotate s).read _ _ = k _ * ((posDir i.2).rotate s).read _ _ * (k _)⁻¹
  rw [Step.gauge_read, Step.vec_rotate,Step.vec_pos]; congr 3
  unfold affine; rw [s.act_add]; abel

abbrev Key (n : Side) := Signed × Cell n
namespace Key
variable (i : Key n)
def native := i.2.1
def frame (U : Config G n) := pull i.1 i.native U
def root : Cell n := (0,i.2.2)
def positive := Face.send i.1 i.native i.root
def skin : Support n := (touched i.root).image (affine i.1 i.native)

def perm (s : Signed) (x : Site n) : Equiv.Perm (Key n) := Equiv.prodCongr (Equiv.mulLeft s)
    (Equiv.prodCongr (frameSites s x) (Equiv.refl PlaqAxes))

theorem oriented (s : Signed) (x : Site n) (U : Config G n) : (perm s x i).frame U = i.frame (pull s x U) :=
  (pull_pull ..).symm

theorem spun (s : Signed) (x : Site n) : (perm s x i).skin = i.skin.image (affine s x) := by
  change (touched i.root).image (affine (s*i.1) (affine s x i.native)) = _
  rw [skin,Finset.image_image]
  congr 1; funext p; simp [affine,Signed.act_mul,add_assoc]

theorem spins_healthy (U : Config G n) (t : ℝ) : Healthy t i.skin U ↔ Healthy t (touched i.root) (i.frame U) := by
  rw [Healthy,skin,← H03.flags_send i.1 i.native t U,Finset.disjoint_image (aff_inj ..)]
  rfl

theorem skin_positive : i.skin = touched i.positive := (H03.touched_send ..).symm

theorem native_mem : i.native ∈ i.skin := by
  have h := Finset.mem_image_of_mem (affine i.1 i.native) (anchor_visit i.root)
  simpa [affine,show i.root.1=0 from rfl,skin] using h

theorem nearby {x : Site n} (h : x ∈ i.skin) : separation i.native x ≤ 2 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
  have he : i.native = affine i.1 i.native i.root.1 := by simp [root,affine]
  rw [separation_comm]; nth_rw 1 [affine]; nth_rw 2 [he]; rw [affine,separation_translate,separation_signed]
  exact visit_near i.root hp

def owed (U : Config G n) := due c b (i.frame U) i.root

def addrE : RegularAddress n := ⟨i.native,i.skin,i.native_mem⟩

def accrual (U : Config G n) := residual G i.root (i.frame U)

theorem accrual_def : i.accrual = residual G i.positive := funext fun U => (residual_send _ _ _ U).symm

theorem readable {D : ℕ} (U V : Config G n) (h : Agrees (halo D {i.native}) U V) (p : Cell n)
    (hp : separation 0 p.1 + 2 ≤ D) : faceValue U (Face.send i.1 i.native p) = faceValue V (Face.send i.1 i.native p) := by
  apply face_local _ U V (agrees_mono h _)
  intro z hz
  rw [Finset.mem_coe, H03.touched_send] at hz
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  rw [Finset.mem_coe,halo_spec]; refine ⟨i.native, Finset.mem_singleton_self _,?_⟩
  have he : i.native = affine i.1 i.native (0:Site n) := by simp [affine]
  nth_rw 1 [he]; simp only [affine,separation_translate,separation_signed]
  apply (separation_triangle 0 p.1 q).trans (le_trans _ hp)
  rw [separation_comm p.1]; exact Nat.add_le_add_left (visit_near p hq) _

theorem kept_reads (h : Decent c b) : LocalOn (halo b.B {i.native}) (fun U : Config G n =>
      decide (PathData.kept c b.threshold 0 (i.frame U))) := by
  intro U V he
  suffices PathData.kept c b.threshold 0 (i.frame U) ↔ PathData.kept c b.threshold 0 (i.frame V) from decide_eq_decide.mpr this
  apply forall_congr'; intro p
  by_cases hp : separation 0 p.1 + 2 ≤ b.B
  · have hu (U : Config G n) := Face.send_price U p i.1 i.native G.chord G.chord_inv fun k g => G.chord_conj g k
    simp only [frame,hu,i.readable U V he p hp]
  exact iff_of_true (too_far c b h _ _ _ (by omega)) (too_far c b h _ _ _ (by omega))

theorem owed_reads (h : Decent c b) : UsesFinal b.threshold (halo b.B {i.native}) (owed c b i (G:=G)) := by
  intro U V he hf
  have ht := kept_reads c b i h U V he
  have hr := i.readable U V he i.root (by simpa [root] using h.radius)
  have hc (W : Config G n) := Face.send_price W i.root i.1 i.native G.chord G.chord_inv fun k g => G.chord_conj g k
  have hp (W : Config G n) := Face.send_price W i.root i.1 i.native G.price G.price_inv fun k g => G.price_conj g k
  have hk (W : Config G n) := Face.send_price W i.root i.1 i.native (fun w => ‖G.curvature w‖)
    (by simp) (fun k g => by simp [Gauge.curvature_conjugate])
  have hE : i.skin ⊆ halo b.B {i.native} := fun z hz => halo_spec.mpr
    ⟨_,Finset.mem_singleton_self _,(i.nearby hz).trans h.radius⟩
  have hL : Healthy b.threshold i.skin U = Healthy b.threshold i.skin V := by
    refine H03.reads_larger hE (fun X Y _ hY => ?_) U V he hf
    unfold Healthy
    simpa [Finset.disjoint_iff_inter_eq_empty] using (show (i.skin ∩ flags b.threshold X = ∅) =
      (i.skin ∩ flags b.threshold Y = ∅) from by rw [hY])
  simp only [decide_eq_decide] at ht
  simp only [owed,due,← spins_healthy,show i.root.1=0 from rfl,hL,ht]
  simp only [frame,hc,hp,hk,hr]

theorem owed_gauge (U : Config G n) (k : Site n → G.El) : owed c b i (gauge k U) = owed c b i U := by
  unfold owed frame; rw [pulls_gauge,due_gauge]

theorem owed_zero {U : Config G n} (h : Decent c b) (hd : i.native ∉ halo b.B (flags b.threshold U)) : owed c b i U = 0 := by
  rw [halo_spec] at hd
  have hf {z : Site n} (hz : separation i.native z ≤ b.B) : z ∉ flags b.threshold U := by
    intro he; exact hd ⟨z,he,(separation_comm _ _) ▸ hz⟩
  have hh : Healthy b.threshold (touched i.root) (i.frame U) := (spins_healthy i U _).mp <|
    Finset.disjoint_left.mpr fun z hz => hf ((i.nearby hz).trans h.radius)
  have ht : PathData.kept c b.threshold i.root.1 (i.frame U) := by
    intro p
    by_cases hp : separation i.root.1 p.1 ≤ b.B
    · have hr : G.chord (faceValue (i.frame U) p) ≤ b.threshold := by
        by_contra! he
        have hv := Finset.mem_image_of_mem (affine i.1 i.native) ((flags_spec ..).mpr ⟨p, anchor_visit p, he⟩)
        rw [frame,H03.flags_send] at hv
        refine hf ?_ hv
        simpa [affine,root,Signed.act_zero,zero_add] using (show
          separation (affine i.1 i.native i.root.1) (affine i.1 i.native p.1) ≤ b.B by simpa [affine] using hp)
      exact hr.trans (le_mul_of_one_le_right b.threshold_pos.le (Real.one_le_exp <| div_nonneg (by positivity) c.radius_pos.le))
    exact too_far c b h _ _ _ (by omega)
  unfold owed due; rw [if_neg (not_lt.mpr (healthy_chord i.root _ hh)),if_pos hh,if_pos ht,sub_self]
end Key
end YM.WilsonStartup

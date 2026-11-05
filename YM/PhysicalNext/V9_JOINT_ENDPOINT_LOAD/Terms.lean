import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Endpoints
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Provision
import YM.Extra.WILSON_STARTUP.MixPay
import YM.Next.UV_STRESS.Glide
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Enrollment
import YM.Push.STATIONARY_UNIFORM.Tame
import YM.Push.STRESS_FLUX.Orbits
import YM.UVNext.COUPLING_RESET.Advance



/-!
# Individual realization & cost of ALL Z-loaded optionals of this currency

Signs/admissible families in the first expansion of `glass`, at correct
flags; genuine coefficient *values* even before choosing the local germs
for the held-U calculation. Uses full endpoint color blocks, not coloring
Mayer factors independently. `Terms`/`Pose` = UPSTREAM ports (not outputs!)
for the selected-word + single-law read dictionary. Other entries (receipts,
gates and scalar letters) retain their exact analytic purchase obligations in
the consumer. `Pose` permits the good extension on threshold equality as in E,
only at its own tested use; MUST agree even about this Reel for a Wakes test,
equality just of fog at V wouldn't prove this. No reconstruction of a local
kernel, mean or factor dictionary here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Matrix Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Spot Spot.Programme Notice
open Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism
open AnalyticBridge.SectorAffine (Offset.mean)
open Push.SectorMeasure Wisps Schur
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {u : Spot d} {A : Stores S} {F : Forest S.ratio} {κ : S.Choices}
  {X : Support c} {H R K α β γ : Type} {l : Viewport u X H R K} {D : u.Slices} {b : Finset ℕ}
  {q : Programme D b} {n : q.Run α β γ} {s : Seats l n} {a : Notice l} {B : Reading a n}
  {P : Patch} {V : Config G c} {v : Charges} {cap : ℝ} {k : ℕ}

abbrev At (v : Charges) (u : Spot d) (V : Config G c) (k : ℕ) :=
  Value v d.betaHat d.radius d.tube u.A u.F u.k V d.out k d.broadCut d.g

def Sseries (u : Spot d) (e : Serial u.ActiveKey) (V : Config G c) (i j : u.InKey) :=
  Function.extend (e i.1 j.1) (fun ⟨zeta,t⟩ => block d.tube u.A u.F d.betaHat u.k (zeta+1) i.1 t j.1 i.2 j.2 V) 0

lemma Value.correct (h : At v u V k) (hu : u=spectacle d A F κ) (hl : Limits v S.patch G cap d.betaHat)
    (e : Serial u.ActiveKey) (i j : u.InKey) : HasSum (Sseries u e V i j) (((u.C V)⁻¹-u.shiftGram V) i j) := by
  apply (hasSum_extend_zero (e i.1 j.1).injective).mpr
  subst u
  exact h.expands rfl hl.paths hl.bounded ..

/-- Auxiliary arbitrary completion only used with agreements over the FULL
Y, never optimizing a tail estimate on those extra links. -/
def rear (l : Viewport u X H R K) (p : LinkArray G K) : LinkArray G u.FrozenKey := Function.extend l.held p 1
def madeup (l : Viewport u X H R K) (y : Display G H R K) : u.Visual := (rear l y.1,Function.extend l.slot y.2 0)
lemma madeup_info (l : Viewport u X H R K) (y : Display G H R K) : l.info (madeup l y)=y := by
  apply Prod.ext
  · exact funext (fun _ => l.held.injective.extend_apply ..)
  exact funext (fun _ => l.slot_inj.extend_apply ..)

def vapors (l : Viewport u X H R K) (z : Position (H⊕R) u.ActiveKey) : Config G c → Display G H R K → ℝ :=
  z.elim (fun i => lin (fun b W p => headwind d.tube d.betaHat u.A u.F u.k d.broadCut d.radius d.g (rear l p) W (l.slot (i,b))) i)
    (fun ⟨zeta,⟨i,j⟩,t⟩ => dual (fun a b W _ => block d.tube u.A u.F d.betaHat u.k (zeta+1) (l.read i) t (l.read j) a b W) i j)

/-- Exact address convention for Z pieces of `u.cardCost`. The `Series`
condition at (physical) V really can be used in Slices.correction: see
`Value.correct`. DOES NOT assume the suppliers of OTHER logs. Identity
with unclamped η at V here follows from the sector prices. -/
structure Terms (s : Seats l n) (V : Config G c) : Prop where
  numbered : D.difference V = Sseries u s.number V
  literal (i : Full u.ActiveKey) (p : u.Visual) : let j := address u s.number i; q.posted j V p=u.price D j V p

namespace Terms
private lemma windy (hB : At v u V k) (hu : u=spectacle d A F κ) (p : u.Visual) : u.sourceFee V p=headwind d.tube d.betaHat u.A u.F u.k d.broadCut d.radius d.g p.1 V := by
  subst u; exact (hB.source p.1).2.symm

lemma spells (h : Terms s V) (hB : At v u V k) (hu : u=spectacle d A F κ) (hV : u.Clearing V)
    (B : Reading a n) {j i} (hp : s.tag j=some i) (y : Display G H R K) : B.delta j V y = vapors l i V y := by
  let p := madeup l y
  have ht := s.tagged.mp hp
  calc
    B.delta j V y = q.posted (n.marks j) V p := madeup_info l y ▸ B.deltaReached j V p hV
    _ = u.price D (address u s.number (project l i)) V p := ht ▸ h.literal (project l i) p
    _ = _ := by
      cases i with
      | inl i =>
        change (∑ a:G.ColorIndex,u.sourceFee V p (l.slot (i,a))*p.2 (l.slot (i,a))) = _
        have he : u.sourceFee V p=headwind d.tube d.betaHat u.A u.F u.k d.broadCut d.radius d.g (rear l y.1) V := windy hB hu p
        rw [he]; change _ = ∑ a:G.ColorIndex, _ * _
        apply Finset.sum_congr rfl; intro a _
        rw [show p.2 (l.slot (i,a))=y.2 (i,a) from l.slot_inj.extend_apply ..]
      | inr j =>
        rcases j with ⟨m',⟨i,j⟩,t⟩
        let Y := l.read i; let Z := l.read j
        let N := s.number Y Z ⟨m',t⟩
        have he b b' : D.difference V (l.slot (i,b)) (l.slot (j,b')) N =
            block d.tube u.A u.F d.betaHat u.k (m'+1) Y t Z b b' V := by rw [h.numbered]; exact (s.number Y Z).injective.extend_apply ..
        change (∑ a:G.ColorIndex,∑ b:G.ColorIndex, (p.2 (l.slot (i,a))*(D.difference V (l.slot (i,a)) (l.slot (j,b)) N*p.2 (l.slot (j,b))))/2) = _
        simp_rw [he, show ∀ i,p.2 (l.slot i)=y.2 i from fun i => l.slot_inj.extend_apply ..]; rfl
end Terms

/-- Required *germ* agreement of the held reads with the very same selected
smooth expressions (even if V is on a boundary). Holding all required U hard
arguments simultaneously is the upstream job; NOT assuming any of the ticket
estimates on these movements/letters. No field jet of a moving-tag choice.
-/
structure Pose [Fintype H] [Fintype R] (B : Reading a n) (s : Seats l n) (V : Config G c) (p : Reel G H R K) : Prop where
  drawn (j i) : s.tag j=some i → (fun W => B.delta j W (p.1,a.imprint W p)) =ᶠ[𝓝 V] fun W => vapors l i W (p.1,a.imprint W p)
  agreed i b : a.harvested p i b =ᶠ[𝓝 V] fun W => AnalyticBridge.SectorAffine.Offset.mean d.tube d.betaHat u.k u.A u.F d.broadCut d.radius (rear l p.1) W (l.slot (Sum.inl i,b))

variable [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ]
  (M : Income α β γ (H⊕R)) {o : Site c} {t θ L W : ℝ}

namespace Pose
variable {p : Reel G H R K} (hs : Pose B s V p) {ok : u.ActiveKey → Prop} (hv : ∀ i,ok (l.read i))
    (h : Part ok v d.radius d.tube u.k V d.out k d.broadCut d.g)
    (hP : Studio d.chart t k L W) (hh : Needed l t V p)
include hs hv h hP hh
omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq H] [DecidableEq R] [DecidableEq γ] in
lemma motions_part (i : H) (b : G.ColorIndex) : Charge (d.out.dirBound o) k V (motionBill v l o L k (i,b)) (a.movement p (Sum.inl i,b)) := by
  have hb := (warming hP V hh i o).linear (Notice.term G b)
  have ht := ((h.moving o (l.slot (Sum.inl i,b)) (rear l p.1) (hv _)).1.agree (hs.agreed i b).symm).indiv (-(d.g)⁻¹)
  rw [a.hailed]
  convert! (hb.tip.indiv d.g⁻¹).add ht.tip using 1
  · rw [norm_neg]; rfl
  ext Y; erw [Pi.add_apply, smul_sub, Notice.translated b, neg_smul]; abel

omit [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq H] [DecidableEq R] [DecidableEq γ] in
lemma motions_local (j : Component G H R) : Charge (d.out.dirBound o) k V (totalBill s v M o L k) (a.movement p j) := by
  have he := totalBill_pays s v M o L k
  rcases j with ⟨i|i,b⟩
  swap
  · rw [a.vacated]; exact Charge.freeze _ (zero_le_one.trans he.1)
  exact (hs.motions_part hv h hP hh i b).radius (he.2.2.2.1 (i,b))

omit [Fintype α] [Fintype β] [DecidableEq β] in
lemma billed_local (j : γ) (hz : j∈s.big)
    (hw : ∀ n (i h : H⊕R) (f : Tracks u.ActiveKey n), s.place ⟨j,hz⟩=Sum.inr ⟨n,(i,h),f⟩ → ∀ t,ok (f t)) :
    let rc := (hire s v M o L k θ cap).rents
    let z := a.imprint V p
    Ticket (d.out.dirBound o) k V (rc.quota j z) (rc.grow z) (fun W => B.delta j W (p.1,a.imprint W p)) := by
  intro rc z
  let T := totalBill s v M o L k
  obtain ⟨ht,-,ho,-⟩ := totalBill_pays s v M o L k
  have hρ : 3*T ≤ rc.grow z := le_mul_of_one_le_right (show 0≤3*T by unfold T; linarith) (one_le_pow₀ (Moments.grows z))
  let Y := s.sits j
  have hy : ∀ i∈Y, Ticket (d.out.dirBound o) k V (ballast 1 Y z) T (a.movement p i) :=
    endpoint (fun i _ => hs.motions_local M hv h hP hh i) le_rfl (fun i hi=>buoys Y z hi le_rfl)
  let t' := s.place ⟨j,hz⟩; have hi := s.place_is ⟨j,hz⟩
  apply Ticket.agree ?_ ((hs.drawn j _ hi).symm)
  change Ticket _ _ _ (rc.quota j z) _ (fun w => vapors l t' w (p.1,a.imprint w p))
  rw [show rc.quota j z = (v.pay d.betaHat u.A u.F G (project l t'))^2 * floorPrice Y z from
    ((if_pos hz).trans (congr_arg (fun t : ℝ => t^2*floorPrice Y z) (s.stipend_big v M ⟨j,hz⟩)))]
  have hY : Y={(legs t').1,(legs t').2} ×ˢ Finset.univ := s.sits_big ⟨j,hz⟩
  have hx := ho ⟨j,hz⟩
  change (project l t').elim _ _ ≤ T at hx
  have ht0 : 0 ≤ T := zero_le_one.trans ht
  cases heq : t' with
  | inr pos =>
    rcases pos with ⟨m',⟨i,j'⟩,f'⟩
    rw [heq] at hY hx
    let c := blockPrice v u.A u.F G d.betaHat (m'+1) (l.read i) f' (l.read j')
    refine (par (F:=fun b c w _ => block d.tube u.A u.F d.betaHat u.k (m'+1) (l.read i) f' (l.read j') b c w) (i:=i) (j:=j') (C:=c) ?_ ht0 hy ?_).mono ?_ hρ
    · intro b; simp [hY,legs]
    · intro a b; exact (h.block_ticket (m'+1) _ _ _ a b o (hv _) (hw m' i j' f' heq) (hv _)).mono le_rfl hx
    simp only [one_pow,mul_one]; exact mul_le_mul_of_nonneg_right (v.walk_covers ..) (zero_le_one.trans (inPrice ..))
  | inl i =>
    rw [heq] at hY hx
    refine (line (E:=fun b w y => headwind d.tube d.betaHat u.A u.F u.k d.broadCut d.radius d.g (rear l y) w (l.slot (i,b))) (i:=i) ?_ ht0 hy (fun b => ((h.moving o (l.slot (i,b)) (rear l p.1) (hv _)).2.mono le_rfl hx))).mono ?_ ((by linarith : 2*T≤3*T).trans hρ)
    · intro b; simp [hY,legs]
    · set Q := floorPrice Y z
      have hQ : 1 ≤ Q := inPrice ..
      rw [← mul_assoc,ballast,one_mul]
      change _*Real.sqrt Q ≤ _^2*Q
      exact mul_le_mul (v.solo_covers G _) (show Real.sqrt Q ≤ Q by rw [Real.sqrt_le_left (by linarith)]; nlinarith) (Real.sqrt_nonneg _) (sq_nonneg _)
end Pose

namespace Pose
variable {p : Reel G H R K} (hs : Pose B s V p) (h : At v u V k)
    (hP : Studio d.chart t k L W) (hh : Needed l t V p)
include hs h hP hh
omit [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq H] [DecidableEq R] [DecidableEq γ] in
lemma motions (j : Component G H R) : Charge (d.out.dirBound o) k V (totalBill s v M o L k) (a.movement p j) :=
  hs.motions_local M (ok:=fun _=> True) (fun _=>trivial) (h.parts _) hP hh j

omit [Fintype α] [Fintype β] [DecidableEq β] in
lemma billed (j : γ) (hz : j∈s.big) :
    let rc := (hire s v M o L k θ cap).rents
    let z := a.imprint V p
    Ticket (d.out.dirBound o) k V (rc.quota j z) (rc.grow z) (fun W => B.delta j W (p.1,a.imprint W p)) :=
  hs.billed_local M (ok:=fun _=> True) (fun _=>trivial) (h.parts _) hP hh j hz (fun _ _ _ _ _ _=>trivial)
end Pose
end YM.PhysicalNext.JointLoad

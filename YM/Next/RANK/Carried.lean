import YM.Next.RANK.Insiders
import YM.Next.RANK.Instructions
import YM.Next.RANK.Motor
import YM.Next.RANK.Stories


/-!
# Primary calibration against regular germ of old masks

Trim lectures with real axis Snap. Long histories in density expression are
retained for W value use separately; only apply projection to the short
ones. On old supports even at integer period, align true physical H.J.
Nonwrapping and all actual gauges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Asymptotics Filter Lattice Wilson RG Extraction Labels Source Source.Drops
open Configuration Normal Rise LiftMark Tariffs MvPolynomial MeasureTheory
open scoped ContDiff Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) {N p k d m D b : ℕ} (i : ℕ) (v : C.label d)
variable (h : C.Makes) (hk : C.ref d ≤ k) (hN : k ≤ N)

def lightKey (u : LA C d) : C.label d := Sum.elim (fun _ => (C.labels.level d).e0) (fun j=> Pi.single j 1) u

def lowKey (v : C.label d) (i k N p) : nearIndex C v i k N p → C.label d := Sum.elim (lightKey C) (fun _=>0)

lemma cult (k N p : ℕ) :
    let F:=C.labels.level d; let P' := C.path.rep N p k; let z:= parcel C d k N p v
    z.x 0 • F.e0 + F.scaled P'.p.threshold⁻¹ (F.core z.x) = ∑ i:LA C d, verseW C v k N p i • lightKey C i := by
  intro F P z; unfold LA; rw [Fintype.sum_sum_type, Fintype.sum_unique]
  refine congr_arg (z.x 0 • F.e0 + ·) ?_
  let x:= F.scaled P.p.threshold⁻¹ (F.core z.x)
  change x=∑ i, x i • Pi.single i 1
  funext i; simp [Pi.single_apply]

lemma sumsKey (P : BudgetPoint) (hp : P=(C.path.rep N p k).p) : ∑ i:LA C d, (pinHat C d k * verseW C v k N p i) •
    ((C.labels.level d).scaled P.threshold (lightKey C i)) = Price.awake C d k N p v := by
  let F:= C.labels.level d; let s:= pinHat C d k; let z:= parcel C d k N p v; let t:= P.threshold
  have ht := P.threshold_pos
  change (∑ i:LA C d,(s*verseW C v k N p i) • (F.scaled t (lightKey C i)))=_
  simp_rw [← smul_smul s,← _root_.map_smul (F.scaled t)]
  rw [← _root_.map_sum,← Finset.smul_sum, ← show z.x 0 • F.e0+F.scaled t⁻¹ (F.core z.x)=∑ i:LA C d, verseW C v k N p i • lightKey C i from ?_, map_smul,map_add,map_smul, Frame.scaled_unit,
    F.scaled_inv (show t≠0 from ht.ne')]
  · change s • (z.x 0 • F.e0 + F.core z.x) = s • z.x
    have he : z.x 0 • F.e0+ F.core z.x=z.x := by ext1 i; by_cases h : i=0 <;> simp [h,Frame.e0, Frame.core, Function.update]
    rw [he]
  unfold t; rw [hp]; exact cult ..

variable {C h hk hN}

-- relative support/orient tests.
structure Provision (C : Family G) (d k N p i R : ℕ) : Prop where
  footprint : (C.localSection d).stencil ⊆ box R
  cap : 10*R<(C.side k p).val
  cuts : i*(4*(C.path.rep N p k).p.B+2)+2*(C.path.rep N p k).p.B ≤ R
  length : 2*(R+1)<(C.side k p).val

include h hk hN
variable {i v}
lemma Provision.contained (H : Provision C d k N p i b) (v : C.label d) (a : nearIndex C v i k N p) :
    nearX C v i k N p a ⊆ patch b 0 := by
  have hb := h.calibrated d N p (hk.trans hN)
  rcases a with (u|u)|u
  · intro i hx; rw [show i=0 from Finset.mem_singleton.mp hx,doors, separation_self]; exact Nat.zero_le _
  · rw [patch_eq]; exact Finset.image_subset_image H.footprint
  intro j hj; rw [doors]
  let P:= parcel C d k N p v
  let W := (C.path.rep N p k).p
  refine (Corona.extent (P.support u.val) W.B ?_ hj).trans ?_
  exact (hb.format k hk hN _).origin _
  exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ u.property) _).trans H.cuts

omit hk hN in
lemma covering (H : Provision C d k N p i b) (c : C.label d) (A : Snap G d) (t : ℝ) :
    let p:= (fun r=> (C.localSection d).places c (0:Site (C.side k p)) (south C.params 0 A t r)); let Z:= (fun r=> Labels.read (scaleJet (expand d (t • A)) r) ((C.labels.level d).coords.symm c).val)
    ContDiffAt ℝ d p 0 ∧ ContDiffAt ℝ d Z 0 ∧ asym d (p-Z) := by
  let a : Jet G:=expand d (t • A); let o : Site (C.side k p) := 0
  obtain ⟨C₀,hP,he⟩:= (h.sections d).projects c a
  intro g Y
  rw [show g=(fun r=> (C.localSection d).evaluate c (C.params.links d a r)) from ?_]
  · refine ⟨C₀,hP,depth C₀ hP he⟩
  funext i
  apply (C.localSection d).cylinder_local
  intro e hi hx; exact content H.length C.params a d i _ (H.footprint hi) (H.footprint hx)
omit h hk hN

lemma change_kp (A : Snap G d) (t : ℝ) (v) : kp d (t • A) v=(t:ℂ)*kp d A v := by
  have hi:= (spanKey d v).isLt; unfold kp Labels.coord; simp only [expand,dif_pos (show v.val.1<d-1 from hi),Pi.smul_apply,Finsupp.smul_apply, _root_.map_smul,Finsupp.smul_apply,smul_eq_mul, Complex.ofReal_mul]
lemma clothes (F : Frame G d) (A : Snap G d) (t : ℝ) (x : F.Coeff) :
    aeval (kp d (t • A)) (Tariffs.expose F x)=aeval (kp d A) (expose F (F.scaled t x)) := by
  rw [expose_at,expose_at,weighed_in]
  apply DFunLike.congr_fun (g:=(aeval (R:=ℂ) _).comp (factors _)); ext1 i; simp [change_kp]

lemma industry (h : C.Makes) (hk : C.ref d ≤ k) (hN : k ≤ N) (H : Provision C d k N p i b) (A : Snap G d) (a : nearIndex C v i k N p) :
    let Q:= nearA C v i k N p a
    let F:=C.labels.level d; let t:=(C.path.rep N p k).p.threshold
    let P : ℝ → ℂ := fun r=> Q (south C.params 0 A t r)
    ContDiffAt ℝ d P 0 ∧ evaluate_ray P d= aeval (kp d A) (Tariffs.expose F (F.scaled t (lowKey C v i k N p a))) := by
  intro Q F t P
  rcases a with (a|a)|a
  · have hg : P=fun _=>1 := rfl
    have he : evaluate_ray P d=(1:ℂ) := by
      rw [hg]
      exact total_set d contDiffAt_const ⟨fun i=>if i=0 then 1 else 0,funext fun t=>by simp [Dims,smul_ite]⟩
    change _ ∧ evaluate_ray P d= aeval _ (expose F (F.scaled t F.e0))
    rw [Frame.scaled_unit, expose_at, show F.coords.symm F.e0=Labels.unit G d by rw [← F.coords_unit]; exact F.coords.symm_apply_apply _, show thawKey (unit G d)=1 from map_one _,map_one]; exact ⟨hg ▸ contDiffAt_const,he⟩
  · let y : F.Coeff:= lightKey C (d:=d) (Sum.inr a)
    let Y : ℝ→ℂ:= fun r=> aeval (kp d (flash (t • A) r)) (expose F y)
    obtain ⟨hx,hC,hY⟩ := covering (h:=h) H y A t
    have hz : P=fun r=> (C.localSection d).places y 0 (south C.params (n:=C.side k p) 0 A t r) := rfl
    let q r := Labels.read (scaleJet (expand d (t • A)) r) (F.coords.symm y).val
    have he : q=Y := _root_.funext fun i=> rewrites (F.coords.symm y) (scaleJet (expand d (t • A)) i)
    have hf : asym d (P-q) := hY
    refine ⟨hx,?_⟩
    rw [trill d (show ContDiffAt ℝ d P 0 from hx) (show ContDiffAt ℝ d q 0 from hC) hf,he]
    unfold Y; rw [ray_stamp, show trim (expose F y) _ _ = _ from circle (F.coords.symm y)]
    exact clothes F A t y
  let L:=parcel C d k N p v; let W:= (C.path.rep N p k).p
  have hp := h.calibrated d N p (hk.trans hN); have hf:= hp.format k hk hN ((C.factory d N p).terminal.symm v)
  have hy : Nonwrapping (L.support a.val) 0 := by
    intro x hx
    have he : separation 0 x≤b := (doors (o:=0) x).mp (H.contained (h:=h) (hk:=hk) (hN:=hN) v (Sum.inr a) hx)
    rw [separation_comm]; exact (Nat.mul_le_mul_left 10 he).trans_lt H.cap
  obtain ⟨hs,hh⟩ := (hf.projects a.val hy) (expand d (t • A))
  change _ ∧ evaluate_ray P d=aeval _ (expose F (F.scaled t 0)); rw [map_zero,map_zero,map_zero]
  refine ⟨hs,Finset.sum_eq_zero fun j hj =>?_⟩
  rw [show iteratedDeriv j P 0=_ from hh j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),smul_zero]

-- Exact projection for short summands before suppressing paths
variable {α : nearIndex C v i k N p → ℝ}

lemma purchase_pin (S : Rules G) (h : C.Makes) (hk : C.ref d ≤ k) (hN : k ≤ N) (H : Provision C d k N p i b) {X : ℝ} (L : Normal.poly (links G (0:Site (C.side k p)) b))
    (A : Snap G d) (he : Teller S (0:Site (C.side k p)) b (C.path.rep N p k).p D (nearX C v i k N p) (nearA C v i k N p) (nearW C v i k N p) α X L) (hx : d≤D) :
    evaluate_ray (walked (snips C.params H.length (C.path.rep N p k).p A) L) d = aeval (kp d A) (expose (C.labels.level d) (Price.awake C d k N p v)) := by
  let P:=(C.path.rep N p k).p
  let V:= snips (o:=0) C.params H.length P A
  let w:= nearW C v i k N p
  let F:= C.labels.level d
  obtain ⟨Q,Hq,Hc⟩:= he.produced
  obtain ⟨C',l,hC,Hx⟩ := shades C.params A d D
  obtain ⟨W,hW⟩ := costs_ray d V (Hx _ _ _ H.length P).1
  let N₁:Label G d:= F.coords.symm (Price.awake C d k N p v)
  have hu (a : nearIndex C v i k N p) : W (Q a)= w a* (aeval (kp d A) (expose F (F.scaled P.threshold (lowKey C v i k N p a)))) := by
    let u:= fun r => nearA C v i k N p a (south C.params 0 A P.threshold r)
    obtain ⟨hv,hq⟩ := industry h hk hN H A a
    have heq := ((he.contact a).1)
    obtain ⟨hs,ha⟩:= genuine C.params (nearX C v i k N p a) (nearA C v i k N p a) P (w a) (Q a) S _ (he.smooth a) (H.contained (h:=h) (hk:=hk) (hN:=hN) v a) H.length A (mul_nonneg (norm_nonneg _) heq) hx ((Hc a).2)
    rw [hW,← show evaluate_ray (w a • u) d=evaluate_ray _ d from trill d ((contDiffAt_const (c:=w a)).smul hv) hs ha,← hq]
    change _= _*evaluate_ray u d
    have he i (hi : i ≤ d): iteratedDeriv i (w a • u) 0=w a • iteratedDeriv i u 0 := iteratedDeriv_const_smul (show ContDiffAt ℝ i u 0 from hv.of_le (by exact_mod_cast hi)) _
    change _=w a • evaluate_ray u d; unfold evaluate_ray; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi => ?_
    rw [he i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),smul_comm]
  change evaluate_ray (walked V L) d = _; rw [← hW, ← (value_at Hq W).tsum_eq]
  let B : nearIndex C v i k N p →ℂ := fun p=> W (Q p)
  have hh:= show (∑' k, B k)= (∑ i : LA C d, B (Sum.inl i)) from ?_
  · rw [hh,← sumsKey C v P rfl,map_sum,map_sum]; apply Finset.sum_congr rfl; intro a ha
    rw [show B _= _ from hu (Sum.inl a)]; simp only [_root_.map_smul]; rfl
  have hb := (Summable.tsum_sum (f:=B) (hasSum_fintype _).summable ((value_at Hq W).summable.comp_injective Sum.inr_injective))
  rw [hb, tsum_fintype]
  have he (j) : B (Sum.inr j)=0 := by rw [show B (Sum.inr j)= _ from hu (Sum.inr j),show lowKey C v i k N p (Sum.inr j) = 0 from rfl]; simp
  simp_rw [he]; simp
end YM.Next.Rank.Spindle

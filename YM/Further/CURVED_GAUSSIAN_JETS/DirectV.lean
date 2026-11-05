import YM.Further.CURVED_GAUSSIAN_JETS.Cutters
import YM.Further.CURVED_GAUSSIAN_JETS.Fares
import YM.Further.CURVED_GAUSSIAN_JETS.Spine

/-!
# Native price for the derivative of each actual oriented affine direct slope
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape
open Green (wt)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {f c n : Side} {S : StepData c f} {F : Forest S.ratio} {I J : Type*} {V : Config G c} {Q : Config G c → ℝ} {k p : ℕ} {C t w : ℝ} (H : Finset F.Free)

structure Sticker (r : Ratio c f) (o x y : Site f) (w t : ℝ) (p k : ℕ) (V : Config G c) (Q : Config G c → ℝ) (C : ℝ) : Prop where
  good : Germ k Q V
  paid (l : List (Directions G c)) : l.length≤k → (∀ d∈l, Due r.embed o p t d) → wt w x y * ‖leftDerivs Q l V‖ ≤ C * cap p t o x ^ l.length

def Items (r : Ratio c f) (o : Site f) (a : I → Site f) (b : J → Site f) (w t : ℝ) (p k : ℕ) (V : Config G c) (A : Config G c → Matrix I J ℝ) (C : ℝ) := ∀ i j, Sticker r o (a i) (b j) w t p k V (fun u=> A u i j) C

lemma single_germ (m : ℕ) (h : Allows 0 (Q ∘ chug 1 V) 0 C) : Germ m Q V := by
  have hm (y : Directions G c) : increment V y=chug 1 V (fun _=>y) := rfl
  have hh : (fun _ : Fin 1 => (0:Directions G c)) = 0 := rfl
  simp_rw [WardBin.Lies.Germ,hm]; exact ((hh.symm ▸ h.analytic).comp (f:=fun y _=>y) 0 (contDiffAt_pi.mpr fun _=>contDiffAt_id)).of_le le_top

lemma sticker_zero (hp : Q = fun _=>0) {o x y : Site f} {r : Ratio c f} (ht : 0 ≤ t) (hC : 0≤C) : Sticker r o x y w t p k V Q C := by
  subst Q; refine ⟨contDiffAt_const,fun l _ _=>?_⟩; rw [Work.G07.left_const]; simp only [ite_self, norm_zero,mul_zero]; unfold cap; positivity
lemma sticker_local {o x y : Site f} {r : Ratio c f} {R : ℕ} (hR : separation x y ≤ R) (hw : 0≤w) (ht : 0 ≤ t) (he : Numerical r.embed x R Q)
    (h : ∀ j≤k+1, Allows j (Q ∘ chug j V) 0 C) : Sticker r o x y w t p k V Q (Real.exp (w*(R:ℝ)) * (C*(1+(R:ℝ))^(p*k))) := by
  refine ⟨single_germ _ ((h 1 (by omega)).order (Nat.zero_le _)),fun l hl hd=>?_⟩
  rw [mul_assoc]; unfold wt
  exact mul_le_mul (Real.exp_monotone (by gcongr)) (he.punch ht hl hd (h _ (by omega))) (norm_nonneg _) (Real.exp_pos _).le

-- test direction CLM on fine links
private def injection : Vec (Bits H G) →ₗ[ℝ] Directions G f where
  toFun x := collect G (test H x)
  map_add' _ _ := by unfold collect; rw [← show (⇑(Shape.translate H G))=test H from rfl, map_add]; rfl
  map_smul' _ _ := by unfold collect; rw [test_smul]; rfl

def insertTest := (injection (G:=G) H).toContinuousLinearMap
lemma insertTest_short (j : Bits H G) : ‖insertTest H (Pi.single j 1)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun b=> (norm_le_pi_norm (test H (Pi.single j 1)) (b.1,coord b.2)).trans (test_unit_norm H j)

def twirl (U : Config G f) (s : Signed) (p : Body 2 f) (v : Directions G f) := G.curvature (faceValue (pull s 0 (increment U v)) ((Cut.turn f).symm p))
def twirlCost (G : Gauge) (k : ℕ) (K : ℝ) := let h {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) := ‖L‖
  h (Ball.paint G) * travelCost G k 4 (fullCost G k K)

lemma twirl_pay {j : ℕ} {K : ℝ} (hk : ExpReceipt G k K) (r : Ratio c f) (V : Config G c) (s : Signed) (p : Body 2 f) (hle : j ≤ k) : Allows k (fun x : joint G c f j=> twirl (replica r (chug j V x.1)) s p x.2) 0 (twirlCost G k K) := by
  unfold twirl faceValue; simp only [travel_pull,← Ball.curvature_eq]
  exact (travel_jets (U:=twoStep r V j) (two_pay r V hk hle (by simp)) _ (by simp [square] : List.length _≤4)).linear (Ball.paint G) le_rfl

lemma basic_pay {j : ℕ} {K : ℝ} (hk : ExpReceipt G (k+1) K) (V : Config G c) (s : Signed) (i : Shape.Page G f 2) (b : Bits H G) (hle : j≤k+1) : Allows k ((fun u=> Shape.basic H (replica S.ratio u) s i b) ∘ chug j V) 0 (twirlCost G (k+1) K) := by
  have he := twirl_pay hk S.ratio V s i.1 hle
  let u : Vec (Bits H G) := Pi.single b (1:ℝ)
  apply Allows.germ (allows_proj (tap_pay (insertTest H u) he (insertTest_short H b)) i.2)
  have hh : Tendsto (fun x : Slab G c j => (x, (0:Directions G f))) (𝓝 0) (𝓝 0) := (continuous_id.prodMk continuous_const).tendsto (0:Slab G c j)
  refine (hh.eventually (he.analytic.eventually (by simp))).mono fun x hx=>?_
  simp only [Function.comp_apply,Shape.basic,Shape.direct,row_unit,tap]
  let U := replica S.ratio (chug j V x)
  exact congr_arg (fun v : G.Color=> v.ofLp i.2) (tap_read (twirl U s i.1) (insertTest H) (((hx.comp (f:=fun y=>(x,y)) 0 (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)) u).symm

lemma replica_near (r : Ratio c f) {U V : Config G c} {m : ℕ} {x : Site f} (h : eqOn r.embed x (m+r.count.val) U V) : Next.Fluctuations.AgreeNear id x m (replica r U) (replica r V) := by
  intro b hb; simp only [id_eq] at hb; have he := Corona.near r b.1; have hx := separation_triangle x b.1 (r.embed (r.parent b.1)); unfold replica; split; rfl; exact h _ (show separation x (r.embed (r.parent b.1)) ≤ _ by omega)

lemma basic_reads (s : Signed) (i : Shape.Page G f 2) (j : Bits H G) : Numerical S.ratio.embed (fineSite s i) (4+S.ratio.count.val) (fun u=> Shape.basic H (replica S.ratio u) s i j) := by
  intro u v hv
  have hh := replica_near S.ratio hv
  suffices he : turnFace (replica S.ratio u) s i.1=turnFace (replica S.ratio v) s i.1 by unfold Shape.basic; simp only [row_unit,Shape.direct,he]
  funext x
  unfold turnFace faceValue; simp_rw [travel_pull]
  refine congr_arg G.curvature ?_
  apply Next.Fluctuations.travel_near id (fun x i=>E03.sep_step x i) _ _ _ _ 4 (by simp [square]); rw [affine,add_zero]; intro b hb; unfold increment; rw [hh b hb]

lemma basic_items (G : Gauge) (P : Patch) (k p : ℕ) {w : ℝ} (hw : 0<w) : ∃ C : ℝ, 0<C ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → ∀ (F : Forest S.ratio) (H : Finset F.Free) (o : Site f) (V : Config G c) {t : ℝ}, 0≤t → ∀ s : Signed, Items S.ratio o (fineSite s) (keySite H) w t p k V (fun u=>Shape.basic H (replica S.ratio u) s) C := by
  let m := k+1
  obtain ⟨K,hK,h⟩ := exp_receipt G (m+1)
  let C := max 1 (twirlCost G (m+1) K)
  let R : ℕ := 4+P.L.val
  have hp := zero_lt_one.trans_le (le_max_left 1 (twirlCost G (m+1) K))
  refine ⟨Real.exp (w*(R:ℝ)) * (C*(1+(R:ℝ))^(p*k)),mul_pos (Real.exp_pos _) (mul_pos hp (by positivity)),fun S hP F H o V t ht s i j =>?_⟩
  have hx : R=4+S.ratio.count.val := by unfold R; rw [←hP]; rfl
  by_cases he : separation (fineSite s i) (keySite H j) ≤ 4
  · apply sticker_local (R:=R) (he.trans (by omega)) hw.le ht (hx ▸ basic_reads H s i j) (fun j' hj=>?_)
    exact ((basic_pay H h V s i j (j:=j') (by omega : j' ≤ m+1)).order hj).mono (le_max_right ..)
  exact sticker_zero (funext (fun _=> basic_range H _ s i j (lt_of_not_ge he))) ht (by have hx : 0<C := hp; positivity)

end YM.Further.CurvedGaussianJets.ChangeV

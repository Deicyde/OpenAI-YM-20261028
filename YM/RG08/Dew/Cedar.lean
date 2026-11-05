import YM.RG08.Dew.Flood

/-!
# Combines receipts on ONE block including true winding. Result is finite
stochastic formal conditional at the flat saddle, never an approximation of
the entire actual integral. Jacob coefficients all from J.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG PertExtension PertExtension.Series GaussianScore Stationary
open Lattice Wilson Bloch Filter MeasureTheory Analysis Function Finset Matrix Precision
open Exterior Tree Next.Free
open scoped Topology ContDiff Classical
variable {c f : Side} (G : Gauge) {P : Patch} (k : KernelChoices) (u : G.ColorIndex) (D : ChartRatio G)
variable {X : Type} [Fintype X] [DecidableEq X]
omit [DecidableEq X] in
lemma priorigrass {F : Reel (Psalm X)} (h : ∀ i,Grass (F i)) (i) : Grass (expEra F i) := by
  unfold expEra; let Y : Op X := fun n=> if n=0 then F else 0
  suffices H : ∀ i b,Grass (priori Y b i) from H i 0
  intro i; induction i using Nat.caseStrongRecOn with
  | zero=> intro b; rw [priori_zero,ingr]; split <;> exact Grass.const _
  | ind i ih=>
    intro b; rw [priori_succ]; apply Grass.scale; apply Grass.list; intro m hm; apply Grass.list; intro p hp
    by_cases hh : p.1=0; · rw [countG,hh,zero_smul,zero_mul]; exact Grass.const 0
    have hy n a : Grass (Y n a) := by unfold Y; split; exact h a; exact Grass.const _
    refine Grass.times ?_ (ih p.2 (by have hx:=mem_antidiagonal.mp hp; omega) _)
    unfold countG; rw [← Nat.cast_smul_eq_nsmul ℝ]; exact (hy _ _).scale _

lemma tree_lodge {P : Patch} {t : Train P.J} {X : Repeated P.L} {A' : FreeResolvent.FaceRow}
    {U : Matrix (Body 1 f) (Body 1 c) ℝ} (hu : f.val=c.val*P.L.val) (h : P.Branches k G) (v : Link G c)
    (hQ : Inputs (linked P k c f hu) U ((pink k.penalty t).acts f) (A'.acts c)) :
    let S:=linked P k c f hu
    (scan (coarseMean G X k t)).acts c *ᵥ v = lodgeP G S.ratio (riseM S G (X.forest S.ratio) U *ᵥ v) v := by
  intro S
  have he := (slice_compute X t h c f hu).2.2.2.2 U A' hQ
  erw [scan_at (g:=S.ratio) (coarseMean G X k t)]
  rw [show installed S.ratio (coarseMean G X k t)=riseM S G (X.forest S.ratio) U by
    ext i j; rw [installed]; erw [he]; simp [repackM,unitSplit, riseM,S]]

lemma stanza_neg {α : Type} [Fintype α] {n : ℕ} (F : Shale α n) (h : Summable F) (m : Side) : stanza (-F) m= -stanza F m := by simpa using stanza_scale (-1) h m

omit [Fintype X] [DecidableEq X] in
lemma aura_at {F G : Reel (Psalm X)} (h : Aura F G) (x : X→ℝ) : Aura (fun i=> F i x) (fun i=> G i x) := by
  refine ⟨congr_fun h.1 x,congr_fun h.2.1 x,fun i=>?_⟩
  have hz:=congr_fun (h.2.2 i) x; rw [Finset.sum_apply] at hz; exact hz

lemma vertex_slope {β : Type} [Fintype β] [DecidableEq β] {M : Matrix X X ℝ} (h : PosDef M)
    (μ:Measure (X →ℝ)) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]
    (A : Matrix (Co c β) X ℝ) (F : Canticle β) (hp : Gets F) (K : Row β β) (hK : Whole K) (hx : K.acts c=A*M⁻¹*Aᵀ)
    (x : PAC β c) :
    let H e:=grand (e+2) (F e) c
    let C:= cloud (K.acts c) H 1
    let G:= upswell K F (some c) 1
    (∀ i,C i x=leaned h μ A x (expEra H i)) ∧ Aura (fun i=>C i x) (fun e=>grand (e+2) (G e) c x) := by
  intro H C G
  obtain ⟨hz,hq⟩:=log_wells hK hp.1 (fun i j=> (hp.2 i j).1) c 1
  refine ⟨fun i=>?_,aura_at hz x⟩
  have hf e : Grass (H e) := Grass.list fun i _=> Grass.base (Hemi.pos (recital (F e i) c))
  unfold C cloud tempo; simp only [Finset.sum_apply,one_pow,one_smul]; exact (dock_wins hx h μ x (priorigrass hf i) _ (fun k he=> hq k i he)).symm

lemma prismQ {L : Side} {M : Matrix X X ℝ} (h : PosDef M) (A : Matrix (Co c (Park G L)) X ℝ)
    (μ:Measure (X →ℝ)) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]
    (Q : Row (Fink G L) (Loc G 1)) {K : Row (Fink G L) (Fink G L)} (hK : Whole K)
    (hq : Whole Q) (hx : (veiled K).acts c=A*M⁻¹*Aᵀ) (F : Canticle (Park G L)) (hp : Gets F) (v : Link G c) :
    let H e:= grand (e+2) (F e) c
    let W:= (scan Q).acts c *ᵥ v
    Aura (fun i=> leaned h μ A W (expEra H i)) (fun e=> -(grand (e+2) (exhale K Q F (some c) e) c v)) := by
  intro H W
  let S:=veiled K
  let L n := -(grand (n+2) (exhale K Q F (some c) n) c v)
  have hs : Whole S:= veiled_whole hK
  let T:= upswell S F (some c) 1
  have hT e : L e=grand (e+2) (T e) c W := by
    unfold L grand; rw [Finset.sum_apply,Finset.sum_apply,← Finset.sum_neg_distrib]
    have hh (r) : Summable (T e r) := (upswell_deck _ hs _ (fun i j=> (hp.2 i j).1) hp.1 (some c) 1|>.2 e r|>.1)
    refine sum_congr rfl (fun r _=> ?_); change -stanza (-scrollL (T e r) (scan Q)) c v=stanza (T e r) c W
    rw [stanza_neg _ (scroll_tune (hh _) (scan_whole hq)).1,Pi.neg_apply,neg_neg,scroll_play (hh _) (scan_whole hq)]
  obtain ⟨ht,hT'⟩ := vertex_slope h μ A F hp S hs hx W
  change Aura (fun i=> leaned h μ A W (expEra H i)) L; rw [funext hT]; exact (show _ from by simp_rw [ht] at hT'; exact hT')
-- same absolute leading data fiber. Estmates NO big torus. VARIABLE MEASURE but all comparisons use same actual base Haar tangent measure.
set_option maxHeartbeats 600000 in
theorem stationary_era (P : Patch) (X : Repeated P.L) (t : Train P.J) (hu : f.val=c.val*P.L.val)
    (m' : FreeResolvent.FaceRow) (U : Matrix (Body 1 f) (Body 1 c) ℝ)
    (hX : Inputs (linked P k c f hu) U ((pink k.penalty t).acts f) (m'.acts c))
    (hp : P.Branches k G) (v : Link G c) (A : Air G) (hA : Gets A) :
    let S:=linked P k c f hu
    let F:=X.forest S.ratio
    let cov:=conditionalCov G X k t; let Q := coarseMean G X k t
    -- E is literal G.Park environment, evaluated only AFTER root-tree
    let B:=awakening u P D k.penalty A
    let E e:= grand (e+2) (B e) c
    let L e:= -(grand (e+2) (exhale cov Q B (some c) e) c v)
    let W:=lodgeP G S.ratio (riseM S G F U *ᵥ v) v
    ∀ (μ:Measure (FreeResolvent.Active G F →ℝ)) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ],
        Aura (fun i=> leaned (forest_precision G k t c f hu hp F) μ (chargeS S F G) W (expEra E i)) L := by
  intro S F cov Q B E L W μ ht hx he
  have hh := forest_precision G k t c f hu hp F
  have hc : Whole cov := (conditional_truth G X k _ hp).1
  have hs : Whole Q := (hc.prod (probe_recites G P k|>.1.flipped)).weight k.penalty
  have hW := Gets_awake P D k u hA
  rw [← show (scan Q).acts c *ᵥ v=W from tree_lodge G k hu hp v hX]; exact prismQ G hh (chargeS S F G) μ Q hc hs (people P k X t hp hu) B hW v
end YM.RG08

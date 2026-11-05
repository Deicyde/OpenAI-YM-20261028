import YM.RG08.Canon.Wild
/-! # Comparing stationary series on one period against the Fk transfer
Don't cancel across theta. All-real germ theta-independent as in Dawn.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G} {σ M Λ : ℝ} {ρ : fieldDir G c 1 → AxisChart G F}
variable {η:ℝ} (v:Stationary.Link G c) {t:S.Choices} {D : ChartRatio G} {L : fieldDir G c 1 → (AxisChart G F)≃L[ℝ] AxisChart G F}
local notation "U" => AxisChart G F
local notation "Y" => F.Slice G
variable {W : Air G} (h : Salvo t F R p ρ η L)
local notation "Θ" => lance v h
local notation "Ψ[" x "]" => weighting x h D

abbrev Wide {X : Type}[MeasurableSpace X][TopologicalSpace X] (x:X) (V : (ℝ→Set X) → ℝ→ℝ) (m:ℝ→ℝ) :=
   ∃ s∈𝓝 x, ∀ A:ℝ→Set X,(∀ᶠ t in 𝓝[>]0, MeasurableSet (A t)∧A t⊆s) → (∃ y∈𝓝 x,∀ᶠ t in 𝓝[>]0, y⊆A t) → Fit 3 (V A) m
abbrev brook (G:Gauge) {S' : StepData c f} (F' : Forest S'.ratio) (g:ℝ→F'.Slice G→ℝ) (A : ℝ→Set (F'.Slice G)) (t:ℝ) := (t^Module.finrank ℝ (AxisChart G F'))⁻¹ * ∫ x in A t,g t x∂F'.order G

variable {Ω:ℝ→(F.Slice G)→ℝ} {u w P:ℝ→ℝ}
lemma brook_walk (he : Wide (1:Y) (fun A=> w*brook G F (fun t x=> Ω t (x*mixL v (S:=S) t F)) A) u) (hw : Wide (1:Y) (fun A=> w*brook G F Ω A) P) : Fit 3 u P := by
  obtain ⟨s,hs,H⟩:=he; obtain ⟨q,hq,T⟩:=hw
  let e t:= Homeomorph.mulRight (mixL v t F)
  have he (t) : MeasurePreserving (e t) (F.order G) (F.order G):=measurePreserving_pi (ι:=F.Free) _ _ fun i=> measurePreserving_mul_right G.probHaar ((mixL v t F) i)
  have hp : mixL v 0 F=1 := by unfold mixL; simp; rfl
  have hm : Continuous (fun t:ℝ=> mixL v t F):= by
    apply continuous_pi; intro i; unfold mixL replica; split
    · exact continuous_const
    exact (continuous_apply _).comp (input_cont.comp (continuous_id.smul continuous_const))
  have hj := (hm.tendsto 0).comp (continuous_fst.tendsto ((0:ℝ),(1:Y))); rw [hp] at hj
  have hu := continuous_snd.tendsto ((0:ℝ),(1:Y))
  obtain ⟨d,hd,hv,ha,hB,y,hy,ht⟩:= incline s q hs hq e (by simpa using! hu.mul hj) (by simpa using! hu.mul hj.inv) (fun t x=> Ω t (e t x)) Ω (Eventually.of_forall fun _=> rfl)
  let C:= fun z=> e z '' d
  refine (H (fun _=> d) (Eventually.of_forall fun z=> ⟨ha.measurableSet,hv⟩) ⟨d,hd,Eventually.of_forall fun z=> le_rfl⟩|>.turn).join (Fit.join (Fit.supply ?_ _) (T C (hB.mono fun t ht=> ⟨(e t|>.isOpenMap _ ha).measurableSet,ht.1⟩) ⟨y,hy,ht⟩))
  refine Eventually.of_forall fun t=>?_
  unfold C; simp only [Pi.mul_apply,brook]; rw [kohler (e t) (F.order G) (he t) d ha (fun x=> Ω t (x*mixL v t F)) (Ω t) (fun _ _=> rfl)]

lemma brook_bear {K B : FreeResolvent.FaceRow} {A : Matrix (Body 1 f) (Body 1 c) ℝ}{i:G.ColorIndex}{Z: Air G}{V:ℕ→Config G f→ℝ} (hd: LocalRatio D)(hw : R.Bounds p σ M Λ)(hx : S.patch.Branches S.kernel G)
    (hV : ∀ j,Caper (quad G (YM.RG08.hessian K)) W 2 j (V j)) (hR : Cask p R f (quad G (YM.RG08.hessian K)) W)
    (hW : Gets W)(hv : Halt W)(hK : Whole K)(hS : Whole B)(hC : ∀ m,(K.acts m).IsSymm)(hm : ∀ m,(B.acts m).IsSymm) (hs : Inputs S A (K.acts f) (B.acts c)) (hA : (treeMatrix G S F K).PosDef) (hG : G.Simple)
    (hy : ∀ w : Link G c,Aura (fun j=> leaned hA (snow G F) (chargeS S F G) (lodgeP G S.ratio (riseM S G F A *ᵥ w) w) (expEra (surge S G W i D) j)) (fun j=>-grand (j+2) (Z j) c w)) :
    let C:= (∫ x,(crownM hA).kern x ∂snow G F)*hatsScale S F D
    Fit 3 (fun t'=>C*Real.exp (Ψ[v] t'-oblige (quad G (YM.RG08.hessian B)) Z 2 t' v)) (peval (moment (hold G F.Free) (sublet 0 D h) (morsel 0 h V)) 2) := by
  intro C
  let m := moment (hold G F.Free) (sublet 0 D h) (morsel 0 h V)
  let g:= Real.exp ∘ (Ψ[v]); let d:= discPay S G F (fun _=> v) t 2 V
  let b:= peval m 2
  have hg : Bill 0 g:= by
    apply Fit.havePay (Fit.elevate (by exact Fit.toSave (f:=Ψ[v]) (known v h hR hd hw hG hx)) ?_) ?_ (le_refl 0)
    · exact (bill_const (0:ℝ))
    simpa [Function.comp_def] using (bill_const (1:ℝ))
  refine Fit.turn (brook_walk v (u:=b) (Ω:=d) (w:=g) ?_ ?_)
  · unfold b m; rw [show peval (moment (hold G F.Free) (sublet (0:Link G c) D h) (morsel (0:Link G c) h V)) 2=peval (moment (hold G F.Free) (sublet v D h) (morsel v h V)) 2 from funext fun t=>Finset.sum_congr rfl (fun j hj=>congr_arg (fun x:ℝ=>t^j • x) (compare_shore v h hV hR hw hd j (by have hv:=mem_range.mp hj; omega)).symm)]
    exact centered_once v h hV hR hd hw hx
  obtain ⟨s,hQ,H⟩:= unbless S G F A (fun _=>v) t 2 V W Z K B i D hd contDiffAt_const measurable_const hx hV hW hv hK hS hC hm hs hA hy
  refine ⟨s,hQ,fun f hp hi=>?_⟩
  apply ((H f hp hi).right hg).join
  apply Fit.supply; refine Eventually.of_forall fun z => ?_
  simp only [C,g,Function.comp_apply, Pi.mul_apply]; rw [sub_eq_add_neg,Real.exp_add (Ψ[v] z)]; ring

lemma pay_verse (k:ℕ) (v:Link G c) (Q:Pot G 2) (F:Air G): Bill 0 (fun t:ℝ=> oblige Q F k t v) := life_price ((show Continuous (fun t:ℝ=> oblige Q F k t v) from continuous_const.add (continuous_finsetSum _ (fun i _=> (continuous_id.pow i).mul continuous_const))).continuousAt (x:=0)|>.tendsto.mono_left nhdsWithin_le_nhds)
lemma exalts {K B : FreeResolvent.FaceRow} {A : Matrix (Body 1 f) (Body 1 c) ℝ}{i:G.ColorIndex}{Z: Air G}{V:ℕ→Config G f→ℝ} (hd: LocalRatio D)(hw : R.Bounds p σ M Λ)(hx : S.patch.Branches S.kernel G)
    (hV : ∀ j,Caper (quad G (YM.RG08.hessian K)) W 2 j (V j)) (hR : Cask p R f (quad G (YM.RG08.hessian K)) W)
    (hW : Gets W)(hv : Halt W)(hK : Whole K)(hS : Whole B)(hC : ∀ m,(K.acts m).IsSymm)(hm : ∀ m,(B.acts m).IsSymm) (hs : Inputs S A (K.acts f) (B.acts c)) (hA : (treeMatrix G S F K).PosDef) (hG : G.Simple)
    (hy : ∀ w : Link G c,Aura (fun j=> leaned hA (snow G F) (chargeS S F G) (lodgeP G S.ratio (riseM S G F A *ᵥ w) w) (expEra (surge S G W i D) j)) (fun j=>-grand (j+2) (Z j) c w)) :
    let Q:=quad G (YM.RG08.hessian B)
    Fit 5 (fun t' : ℝ => timeP v h t'+t'^2*scent v D h t') (fun t'=>t'^2*(oblige Q Z 2 t' v-oblige Q Z 2 t' (0:Link G c))) := by
  intro Q
  let C:=(∫ x,(crownM hA).kern x ∂snow G F)*hatsScale S F D
  let X (a:Link G c) t := oblige Q Z 2 t a; let P (a:Link G c) t := Ψ[a] t- X a t
  have ht : Fit 3 (C • (Real.exp ∘ P v)) (C • (Real.exp ∘ P 0)) := Fit.join (brook_bear v h hd hw hx hV hR hW hv hK hS hC hm hs hA hG hy) (Fit.turn (brook_bear 0 h hd hw hx hV hR hW hv hK hS hC hm hs hA hG hy))
  have he := ht.scale C⁻¹; have hh:C≠0:= (mul_pos (normSun hA (snow G F)) (pow_pos hd.scale _)).ne'
  rw [inv_smul_smul₀ hh,inv_smul_smul₀ hh] at he
  have hu (a:Link G c):Bill 0 (P a):= by exact bill_add (known a h hR hd hw hG hx) (bill_neg (pay_verse _ a Q Z)) -- sub
  have hz := he.unelevate (hu _) (hu _)
  let D (t:ℝ):= t^2; have HD := hz.right (ruler 2 2 le_rfl)
  unfold Fit
  apply bill_flip HD; filter_upwards [eventually_pos] with t hp; simp only [Pi.mul_apply,Pi.sub_apply,P,weighting,X,timeP,tram_flat h hR hx,smul_zero,scent,spanL,map_zero]; field_simp; ring
end YM.RG08.Canon

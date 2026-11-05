import YM.RG08.Canon.Mesh
/-! # EXTRA packets from canonical base

Re-lift from aggregations to unmasked q-base paths. Costs of these
paths not charged if not using them in a recurrent way. Preserve
prescribed gauge and leading coefficients. Needed for renderers;
only supplies FORMAL committee and path prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths Conductor Virtue Staffer
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {c:ℕ→Side}{m:Side}{V: Air G}{F:Pot G 2} {R:PathData G}{p:Clip}{σ C A B Λ D τ w : ℝ}

lemma all_cart (G : Gauge){j:ℕ}{X : Pot G (j+1)} {W : ∀ m:Side,Link G m → ℝ} (h : cartography G W j) (hp:Tunable X)(hw:Glows X)
    (ht:Tendsto (fun i=> (c i).val) atTop atTop)(H:∀ i, Tensor.coeff (W (c i)) (j+1) 0=recital X (c i)) (m:Side): Tensor.coeff (W m) (j+1) 0=recital X m := by
  obtain ⟨F,b,C,hc,hF⟩:=h
  exact floors_equal (floors_mark (k:=c) (δ:=fun _=>0) (V:=fun i=> W (c i)) (H:=fun i=> W (c i)) (fun i a v b=> by dsimp only; rw [sub_self, norm_zero, mul_zero]) tendsto_const_nhds (Mending.one _ hw) (fun _=>hp) H hc (fun i=> hF (c i)) ht) hp (hF m)
lemma legacy (R : PathData G)(v : Clip): secondTerm v R (1:Config G m)=0:=by
  have hx (b: Face (Per m)): R.ell (1:Config G m) b=0:= by
    unfold PathData.ell; simp_rw [PathData.ellTerms,Slot.atSite,Slot.eval,show ∀ x:Site m, expandAt x (1:Config G m)=1 from fun _=> rfl]; simp [faceValue,Lattice.travel,square,Step.read]
  simp [secondTerm,Patch.average, quadratic,show ∀ i:Signed, pull i 0 (1:Config G m)=1 from fun i=> funext fun v=> by simp [pull,Step.read],hx,faceValue,square]
-- needs both caps even though not claims this particular θ
lemma rides (he : R.Bounds p σ C Λ)(hp : ∀ i,Cask p R (c i) F V)(H:Tendsto (fun i=> (c i).val) atTop atTop)(h:Tunable F)(hv:Glows F)(hx: Gets V)(m:Side): Cask p R m F V:= by
  have hm : AnalyticAt ℝ (classicFn p R (f:=m)) 0:= (strain p R he).analytic
  have hg:= turns_analytic R.loop he.width he.two (m:=m)
  have hl (q r) : Tunable (sector F V q r):= Tune_sector _ _ (fun i j=> (hx.2 i j).1) h q r
  refine ⟨hm.contDiffAt,fun j hj=> ?_,hg.contDiffAt,fun j hj=>?_⟩
  · cases j with
    | zero=> rw [lead_true he 0 (by decide)]; ext1 i; simp [Tensor.coeff,inputSeries, iteratedFDeriv_zero_apply,sector, legacy]
    | succ j=> exact all_cart G (cart_map j he) (hl 0 (j+1)) (fiscal_sector _ _ hx hv _ _) H (fun i=>(hp i).bound (j+1) hj) m
  cases j with
  | zero=>
     change Tensor.coeff (turnSeries (m:=m) R.loop) 0 0= recital _ _
     rw [sector,recital_zero,Tensor.coeff, (rays_jet hg _|>.1 (turns_low R.loop he.width he.two (m:=m))) 0 (by decide),smul_zero]
  | succ j=> exact all_cart G (cart_path j R.loop he.width he.two) (hl 1 _) (fiscal_sector _ _ hx hv _ _) H (fun i=>(hp i).ropes _ hj) m
end YM.RG08.Canon

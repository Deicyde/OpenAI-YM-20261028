import YM.TraceExtension.Pills.Rate
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}
def Drift (H: Type)[NormedAddCommGroup H][NormedSpace ℝ H](F:Config G n→H):Prop:=∀ (X:Type)[NormedAddCommGroup X] [NormedSpace ℝ X](U:X→ Config G n)(x:X), Army U x→ ContDiffAt ℝ ω (F ∘ U) x
structure Clouded (Y:Gal G n)(P:Support n):Prop where
   rises:Y∈rains G n
   stout : LocalOn P Y
   paints (k:Coats G n) U : Y (Lattice.gauge k U)=armor k (Y U)
   toes (i:Lines G n 1) U : i.1∉P→Y U i=0
   wakes: Drift _ Y
variable {P P':Support n}{Y: Gal G n}{F:Peat G n}
lemma say(o:Site n)(r:ℕ) (h:Y∈rains G n): Clouded (lakesY o r Y) (feed o (r+1)):=by
    refine ⟨lake_y o r h,Y_take o r Y,fun _ _=> Y_swept o r h _ _,fun i U hi=> ?_,fun X _ _ W x hw=> Y_warm o r W x hw Y⟩
    obtain ⟨x,b,i⟩:= i; obtain ⟨b,rfl⟩:=axisEquiv.surjective b; change (edgeColor (lakesY o r Y U) (x,b)) i=0; rw [Y_dry o r h U _ (fun hx=> hi (halo_spec.mpr ⟨_,mem_singleton_self o,by change separation o x ≤ r at hx; dsimp only; omega⟩))]; simp
lemma Clouded.wider(h:Clouded Y P)(hp:P⊆P'):Clouded Y P':=⟨h.rises,fun U V hm=> h.stout _ _ (agrees_mono hm hp),h.paints,fun i U hv=> h.toes _ _ fun hx=>hv (hp hx),h.wakes⟩
lemma riddle (h:LocalOn P F)(i:Lines G n 1): LocalOn P (outD F i):=by
    intro U V ht; apply congr_arg (fun g=> fderiv ℝ g 0 (bolt i:Link G n)); ext1 y; exact h _ _ fun i hx he=> by rw[Pi.mul_apply,Pi.mul_apply,ht i hx he]
lemma rill_local (h:LocalOn P F)(hp:LocalOn P Y): LocalOn P (rill F Y):=by
    intro U V he; rw[hail,hail]; exact sum_congr rfl fun i _=> congr_arg₂ (·*·) (congr_fun (hp U V he) i) (riddle h i U V he)
lemma rill_covU (h:Drift _ F)(hf: GaugeInvariant F)(hp: Clouded Y P): GaugeInvariant (rill F Y):=by
    intro k U; let W:=Lattice.gauge k U; let g(y:Link G n):= F (input _ _ y*W); let f(y:Link G n):= F (input _ _ y*U); have hx: f = g ∘ armor k:= funext fun y=> by unfold f g; rw[Function.comp_apply,show input G n (armor k y)*W=_ from armor_go k y U]; exact (hf k _).symm
    have hh: ContDiffAt ℝ ω g 0:=h _ _ _ ((Army.powL (v:=id) contDiffAt_id).mul (Army.park W _)); change fderiv ℝ g 0 (Y _) = fderiv ℝ f 0 _
    rw [hp.paints, hx,fderiv_comp 0 ((map_zero (armor k)).symm ▸ hh.differentiableAt (by simp)) (armor k).differentiableAt,map_zero,(armor k).fderiv];rfl
lemma ride_sure (h:Drift _ F)(i:Lines G n 1): Drift _ (outD F i):=by
    intro X _ _ U x hp; let K(z:X × Link G n):= F (input G n z.2*U z.1); let A: X:=x
    have hu:ContDiffAt ℝ ω K (x,0):=by
        exact h _ _ _ ((Army.powL contDiffAt_snd).mul (show Army (U ∘ Prod.fst) (x,(0:Link G n)) from fun j=> (ContDiffAt.comp (g:=fun y=>G.mat (U y j)) (f:=Prod.fst) (show X × Link G n from (x,0)) (hp j) contDiffAt_fst)))
    obtain ⟨C,hC,H⟩:=exists_allows (s:={(x,(0:Link G n))}) isCompact_singleton (f:=K) (fun i hi=>hi.symm ▸ hu) 1
    exact (priced_partial (x:=x) (n:=0) (f:=K) (a:=bolt i) (H _ (Set.mem_singleton _)) (norm_bolt ..|>.le)).analytic
lemma rill_lit (h:Drift _ F)(hp:Drift _ Y): Drift _ (rill F Y):=by
    intro X _ _ U x ht; unfold Function.comp; simp_rw [hail]; refine ContDiffAt.sum (s:=univ) (fun i _=> (contDiffAt_pi.mp (hp X U x ht) i).mul (ride_sure h i X _ _ ht))
lemma rill_lo (h:Drift _ F)(he: GaugeInvariant F)(hp:Clouded Y P)(hG:G.Simple): rill F Y ∈loom G n:=by
    refine clergyP _ (rill_covU h he hp) (rill_lit h hp.wakes _ (input G n) _ (Army.powL (v:=id) contDiffAt_id)) ?_ hG
    rw[hail]; simp only [show Y 1=0 from hp.rises.2,Pi.zero_apply,zero_mul,sum_const_zero]
lemma stifleW (h:Clouded Y P){r:ℕ}(hp:P⊆sprout 0 r): ∀ v:Link G n, Stifle (Tbody Y *ᵥ v) r := by
    intro v e hv; unfold Tbody; rw [bill_pay]; let X:=Y ∘ input G n; let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Lines G n 1=>ℝ) e
    change L (fderiv ℝ X 0 v)=0; rw [show L _= fderiv ℝ (L ∘ X) 0 v from ?_, show L ∘ X=(fun _=>0) from ?_]; simp; rotate_left
    · have hD : DifferentiableAt ℝ X 0:= (show Cloaked Y from h.rises.1).dye.differentiableAt (by simp); rw[fderiv_comp _ L.differentiableAt hD,L.fderiv];rfl
    funext z; exact (h.wider hp).toes e (input _ _ z) (fun hh=> not_le.mpr hv (by simpa [Turret.sprout,halo_spec,separation] using hh))
end YM.Trace.Pills

import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Prism
import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.Push.LOCAL_SPLITTING.Direct
/-! # Orientation/gauge of the EXPONENT WITHOUT MASKS

This exact step permits exposure at unoriented *reading* addresses and rotated symmetrization. No proof expected on any particular color's integral or pose choice under rotations. The common Θ removes the full banking term with correct path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
    Primitives.HaarLogJets Guard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A : Stores S} {H : Forest S.ratio}
   {P : Teller G} {ρ : Pilot G S x}
namespace Dyed
variable (v : Dyed G S) {o₀ n Λ δ w : ℝ} (e : Wheel c)
local notation "T"=>v.things
local notation "R"=>v.source
local notation "δ'"=>v.arc

lemma banker_turn (x) (V : Config G c): v.loading x (pull e.1 e.2 V)=v.loading x V:= by
  let K (g : Config G c):= ∑ i:PlaqAxes, v.things.down.baseTerm v.things.low v.bp g (0,i)
  have hp (Y : Config G c) : banker T v.bp Y v.source.beta = Real.exp (-v.source.beta * Next.Rank.Alarm.rag K Y):= by
    unfold banker Next.Rank.Alarm.rag averaged; apply congr_arg Real.exp; apply congr_arg (-v.source.beta* ·); apply congr_arg ((Fintype.card Signed:ℝ)⁻¹*·)
    refine sum_congr rfl fun i _=>?_ ; rw [← Next.Rank.Alarm.spin_shift]; dsimp only; rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun x _ => sum_congr rfl fun j _=> Next.Rank.Edition.base_at _ _ _ _
  unfold loading; simp_rw [hp,Next.Rank.Edition.rag_rip]
lemma banker_halo (x) (V : Config G c) (y : Site c→G.El) (ht : P.Funds S T): v.loading x (Lattice.gauge y V)=v.loading x V:= by
  obtain ⟨u,z,hU,hV⟩:=ht.feeds
  have hp (V : Config G c) (y : Site c→G.El) (p : Cell c): v.things.down.baseTerm v.things.low v.bp (Lattice.gauge y V) p=v.things.down.baseTerm v.things.low v.bp V p:= by
    unfold PathData.baseTerm PathData.kept
    simp only [face_gauge,G.chord_conj,Work.F05.ell_gauge (ht.low.symm ▸ hV) V y p,G.norm_adjoint]; congr
  simp_rw [loading,banker,Push.Local.pull_gauge,hp]
-- keep actual displacement at broad stencil for masks and J guard

def tapeAt (ρ : Pilot G S x) := displaced (meanLog ρ.key ρ.park T x ρ.view ρ.tag v.chi v.arc ρ.y.1) (coupling v.source.beta) ρ.y.2
lemma tape_ship (ht : P.Funds S T) (ρ : Pilot G S x) (i): tapeAt v (spires e ρ) i=fiber e.1 e.2 ρ.view S i.val.val (tapeAt v ρ (Locations.active e.1 e.2 ρ.key ρ.park x i)):= by
  obtain ⟨u,z,hU,hV⟩:=ht.feeds
  let Y:=ρ.y
  let I:= Locations.active e.1 e.2 ρ.key ρ.park x; let Z:=spires e ρ; let q:= v.chi; let E:=fan ρ.key ρ.park e.1 e.2 x ρ.view; let m:=meanLog ρ.key ρ.park v.things x ρ.view ρ.tag v.chi v.arc ρ.y.1
  have he : meanLog Z.key Z.park T x Z.view Z.tag v.chi v.arc Z.y.1=E m:= (turned_mean e.1 e.2 ρ.view ρ.tag T x (funds_branch ht) ρ.key ρ.park (ht.high.symm ▸ hU) v.chi v.arc ρ.y.1).ends
  let g:= coupling v.source.beta
  change tape (_ + g • Z.y.2) i=_; rw [he]; change tape (E m+g • E ρ.y.2) _=_; rw [show E m+g • E ρ.y.2=E (m+g • ρ.y.2) from by
    rw [show E (m+g • ρ.y.2)=E m+E (g • ρ.y.2) from Matrix.mulVec_add ..,show E (g • ρ.y.2)=g • E ρ.y.2 from Matrix.mulVec_smul ..]]
  exact move_tape ..
lemma tape_spin (ht : Boosted T P x) (ρ : Pilot G S x) (hp : Matched ρ) (f : Site c→G.El) (i):
    tapeAt v (burnish f ρ) i=G.adjoint (f (S.ratio.parent i.val.val.1)) (tapeAt v ρ i):= by
  let Y:=ρ.y
  let Z:=burnish f ρ; let q:=v.chi; let E:=toGauge f ρ.key ρ.park x; let m:=meanLog ρ.key ρ.park T x ρ.view ρ.tag v.chi v.arc ρ.y.1
  have hc:= ht.fogged Z.key Z.park Z.view Z.tag (hp.bright f)
  have he:meanLog Z.key Z.park T x Z.view Z.tag v.chi v.arc Z.y.1=E *ᵥ m:= by
    simp_rw [mean_endpoint,m]; rw [mean_endpoint]; exact (turned_law f ρ.key ρ.park x P T ρ.view ρ.tag .endpoint ρ.y.1 v.chi v.arc ht.funded hc).1
  change tape (_+ _ • Z.y.2) i=_; rw [he]; change tape (E*ᵥm+ coupling v.source.beta • (E *ᵥ Y.2)) _= _; rw [← mulVec_smul,← mulVec_add]; exact turn_color ..

lemma exporter (ht : P.Funds S T) (hJ : LocalRatio v.ratio) (hd : 0<v.arc) (hD :4*v.arc<v.ratio.radius) (hR : v.source.Lawful o₀ n Λ δ w) (ρ : Pilot G S x) : v.freight (spires e ρ)= v.freight ρ:= by
  obtain ⟨A,F,k,V,y⟩:=ρ; obtain ⟨u,z,hU,hV⟩:=ht.feeds
  let ρ:Pilot G S x:=⟨A,F,k,V,y⟩; let p:=spires e ρ; let C:=fog A F v.things x V k; let U:=top v ρ
  let s:=e.1; let b:=e.2; let q:=p.view; let i :=S.ratio.embed b; let M:=Locations.forest s b F; let D:=book s b A
  have hh : S.patch.Branches S.kernel G:= funds_branch ht
  let E:=Locations.active s b A F x; let t:=onBond (fiber s b V S) (A:=D) (F:=M) (x:=x)
  have hp:fog D M T x q p.tag=warp t E C:= (turned_cov s b V k T x hh A F (ht.high.symm ▸ hU)).fog
  have hu: v.top p=pull s i U:=fans A F s b v.things ht V k v.chi x v.arc v.source.beta y
  have hm: reserve v.chi v.ratio v.arc (v.tapeAt p) = reserve v.chi v.ratio v.arc (v.tapeAt ρ):= by
    refine Fintype.prod_equiv E _ _ fun i=> ?_
    unfold extended p; rw [tape_ship v e ht]
    unfold fiber scatter; split
    next he=>
      apply congr_arg Real.exp; exact log_extended_turn _ true _ hd hJ hD _
    rfl
  let g:=coupling v.source.beta
  have hσ : Fintype.card (Active D x M) = Fintype.card (Active A x F) := Fintype.card_congr E
  have hc : chartCost (fog D M T x q p.tag) g= chartCost C g:= by
    unfold chartCost; rw [hp,warp_det]; simp only [Fintype.card_prod]; -- cast below
    rw [hσ]
  have hz : S.noise v.source.beta (S.prediction (v.top p) p.tag) p.view= S.noise v.source.beta (S.prediction U k) V:= by rw [hu,S.prediction_channel hh, show (S.withinChoice s b) p.tag=k from (S.withinChoice s b).apply_symm_apply k]; exact S.noise_channel s b _ (S.prediction U k) V
  change v.ratio.scale ^ Fintype.card (Active D x M)*chartCost (fog D M T x q p.tag) g*Real.exp (force (fog D M T x q p.tag) p.y.2/2)*reserve _ _ _ (v.tapeAt p)*S.noise v.source.beta (S.prediction (v.top p) p.tag) p.view* Real.exp (v.source.exponent (v.top p))=_
  rw [hσ,hc,hp,show force (warp t E C) p.y.2=force C y.2 from warp_force t E C y.2,hz,hu,hm, Push.Local.exponent_pull ((hR.labels.moves s i).some)]; rfl

lemma rein {ι : Type} [Fintype ι] [DecidableEq ι] (M C : Gaussian.Table ι) (h : M.transpose*M=1) (P : Gaussian.Vec ι) :
    (covView M C).det=C.det ∧ force (covView M C) (M *ᵥ P)=force C P:= by
  unfold covView; constructor
  · have ht:= congr_arg Matrix.det h
    rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at ht
    simp_rw [Matrix.det_mul,det_transpose]; linear_combination C.det*ht
  rw [force,Matrix.mul_inv_rev,Matrix.mul_inv_rev,
    show Mᵀ⁻¹=M from Matrix.inv_eq_right_inv h, show M⁻¹=Mᵀ from Matrix.inv_eq_left_inv h]
  rw [mulVec_mulVec,Matrix.mul_assoc,Matrix.mul_assoc C⁻¹,h, Matrix.mul_one,← Matrix.mulVec_mulVec,
    dotProduct_comm (M *ᵥ _),← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,h]
  simp only [Matrix.one_mulVec]; rfl

lemma moor (ht : Boosted T P x) (hJ : LocalRatio v.ratio) (hd : 0<v.arc) (hD :4*v.arc<v.ratio.radius) (hR : v.source.Lawful o₀ n Λ δ w) (ρ : Pilot G S x) (hV : Matched ρ) (z : Site c→ G.El) : v.freight (burnish z ρ)=v.freight ρ:= by
  obtain ⟨A,F,k,V,y⟩:=ρ
  let ρ:Pilot G S x:=⟨A,F,k,V,y⟩; let p:=burnish z ρ; let C:=fog A F T x V k; let U:=top v ρ; let z':=constantGauge z S.ratio
  let V':=Lattice.gauge z V; let M:=toGauge z A F x; let Y:=fog A F T x V' k
  have hg:=ht.fogged A F V' k (Matched.bright hV z)
  have he : Y=covView M C:= by
    unfold Y C; simp_rw [Q_endpoint]; exact (turned_law z A F x P T V k .endpoint y.1 v.chi v.arc ht.funded hg).2.1
  obtain ⟨hf,h'⟩ := rein M C (ortho z A F x|>.1) y.2
  rw [← he] at hf h'; have ha: top v p=Lattice.gauge z' U:= (winding A F x v.source.beta v.arc V T ht.funded z k v.chi y hg).symm
  have hq: reserve v.chi v.ratio v.arc (v.tapeAt p)=reserve v.chi v.ratio v.arc (v.tapeAt ρ):= by
    refine Finset.prod_congr rfl fun i _=> ?_
    unfold extended p; rw [tape_spin v ht ρ hV]; apply congr_arg Real.exp; exact log_extended_turn _ false _ hd hJ hD _
  let g:=coupling v.source.beta
  change _ * chartCost Y g * Real.exp (force Y (M*ᵥ y.2)/2)*reserve _ _ _ (v.tapeAt p)*S.noise v.source.beta (S.prediction (v.top p) k) V' * Real.exp (v.source.exponent (v.top p))=_
  rw [show chartCost Y g=chartCost C g from by unfold chartCost; rw [hf], h',ha,hq, YM.Push.Local.Kernel.exp_invariant hR]
  have hv: z' ∘ S.ratio.embed=z:= by unfold z' constantGauge; ext; simp [Function.comp_apply, Ratio.embed_parent]
  rw [(choice_gauge ht.produced.branched _ k z').2,hv];
  have hh : S.noise v.source.beta (Lattice.gauge z (S.prediction U k)) V'=S.noise v.source.beta (S.prediction U k) V:= by
    unfold StepData.noise; apply prod_congr rfl; intro i _; unfold StepData.penaltyWeight
    let W:= S.prediction U k
    rw [show V' i*(Lattice.gauge z W i)⁻¹=z i.1*(V i*(W i)⁻¹)*(z i.1)⁻¹ by unfold V' Lattice.gauge; group, G.price_conj]
  rw [hh]; rfl

lemma sparkle {b₀ a C η : ℝ} (ht : Boosted T P x) (hp : Physical.Certified S T x a C η b₀) (hr : v.things.up=v.source.path) (hc : v.things.high=v.source.clip) (hJ : LocalRatio v.ratio)
    (hd : 0<v.arc) (hD :4*v.arc<v.ratio.radius) (hR : v.source.Lawful o₀ n Λ δ w) (hb : 0<v.source.beta) (hΘ : v.bp.threshold=temp x) (ρ : Pilot G S x) (h : Matched ρ) (z : Site c→G.El) :
    spoolLift v (burnish z (spires e ρ))=spoolLift v ρ:= by
  let i:= spires e ρ; let j:= burnish z i; have he:=h.signed e; have hf:= he.bright z
  have hj:loading v x j.view=v.loading x ρ.view:= (banker_halo v _ i.view z ht.funded).trans (banker_turn ..)
  have hx:= cardinal_spin v ht.funded hp hr hc hJ hb hΘ ρ h
  have hy:= cardinal_spin v ht.funded hp hr hc hJ hb hΘ j hf
  apply Real.exp_injective; apply mul_left_cancel₀ hx.1.ne'
  rw [← hx.2]; rw [hj] at hy; change _*Real.exp (spoolLift v j)=_; rw [← hy.2]; exact (moor v ht hJ hd hD hR i he z).trans (exporter v e ht.funded hJ hd hD hR ρ)
end Dyed
end YM.PhysicalNext.InteractingRank.Pump

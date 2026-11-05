import YM.Next.STATIONARY.Level.Recurse
import YM.UVExtension.Projection.Fumes
import YM.UVExtension.Projection.Bend
import YM.UVExtension.Projection.Lodge

/-! Turn schedules into uniform norm and step issuer. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Precision Tree Stationary Filter Function Finset Projection Wilson Bloch Laurent Exterior Supply
open scoped Topology BigOperators ContDiff Matrix Classical Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L}
    {N m:ℕ}
structure Knobs (a : Levels G) where
    widths : ℕ→ℝ
    E : ℕ →ℝ
    loops : ℕ→ℝ
    health m:0<widths m ∧ 0<E m ∧ 0<loops m

def label (D : Knobs a) (m:ℕ): Rates G:= ⟨a.S.side m,D.widths m,D.E m,D.loops m,(D.health _).1,(D.health _).2.1,(D.health _).2.2⟩
variable {D : Knobs a}
abbrev sat (D : Knobs a)(V : Horizon a)(N m:ℕ) (x:Cube G):= (label D m).path (V.H N m) x
structure Working (D : Knobs a)(V:Horizon a)(P : MapPrices) (m : ℕ) : Prop where
    beside N : m≤N → Hull (V.H N m) (P.η (a.clock.J m)) (P.α (a.clock.J m)) (pacesE P (a.clock.J m)) (a.params m).clip (a.S.side m) G
    width1 : (a.params m).width < P.α (a.clock.J m)
    width2 : (a.params m).width < D.widths m/2
    paid N : m≤N→∀ x:Cube G,x∈ (label D m).valid→‖x‖ ≤ 1 → SatPath V N m (sat D V N m x)

theorem organized (h : Working D V P m) : Toned (label D m):=by
  let B:=V.H m m; let i:=a.clock.J m; let p:= a.params m; let E:=label D m; have ht:=p.width_pos
  have hp:=h.beside _ (le_refl m); have hv:=hp.2.2.1
  refine ⟨bound_climb _ _ _,fun x hx=>?_⟩
  let r:= E.path B x; let y:= overhead G E.grainWidth
  let C:= max (E.mold*‖x‖*y) (rowPrice (P.α i) (pacesE P i)); let b:= E.coil*‖x‖*y
  have hr: r.Bounds p.clip p.width C b:= E.takeAny B ht h.width1.le h.width2.le hp.2.1 (hv 1) (le_max_right ..) (le_max_left ..) le_rfl x le_rfl hx
  obtain ⟨hu,he⟩:=filing_ready r hr
  exact ⟨filing r,_,_,ht,fun i=> ⟨turns_analytic _ ht hr.two, he _⟩,hu⟩

section seams
variable {t u : Cube G}
lemma same_classical_path (q:Clip){σ A Λ σ' A' Λ' : ℝ}(Y:Rates G)(M:Bed)(U:Cube G)(W:Cube G)(h:U-W∈Y.seam)(hp:(Y.path M U).Bounds q σ A Λ)(he:(Y.path M W).Bounds q σ' A' Λ') (z:ℝ) (p i:ℕ) (hi:i≤4): SameJet i (fun x:Bid.Dir G (Y.stageSide p) => mainTerm q (Y.path M U) (represent x)) (fun x=> mainTerm q (Y.path M W) (represent x)) ∧ SameJet 2 (draft (c:=Y.stageSide p) z (Y.path M U) q) (draft z (Y.path M W) q):=by
  let K:=arm G (Y.stageSide p) 1
  change Y.Blur _ at h
  have hh:= ell U hp; have hv:= ell W he
  have hA:= h.2 p
  refine ⟨⟨hh,hv,inverts G (Y.stageSide p) _ _ i hh hv ?_⟩,⟨haze_draft _ _ hp,haze_draft _ _ he,inverts G (Y.stageSide p) (draft z (Y.path M U) q) (draft z (Y.path M W) q) 2 (haze_draft _ _ hp) (haze_draft _ _ he) ?_⟩⟩
  · let F:= inputSeries q (Y.path M U) (m:=Y.stageSide p); have hf:ContDiffAt ℝ i F 0:= (stain_knit _ _ hp).analytic.contDiffAt
    change iteratedFDeriv ℝ i (intended q (Y.path M U) (m:=Y.stageSide p)) 0=iteratedFDeriv ℝ i (intended q (Y.path M W) (m:=Y.stageSide p)) 0
    rw [intent,intent,add_assoc,add_assoc]; change iteratedFDeriv ℝ _ (F+Y.hat U p) _=iteratedFDeriv ℝ _ (F+Y.hat W p) _
    rw [iteratedFDeriv_add_apply hf (Y.hat_an U p).contDiffAt,iteratedFDeriv_add_apply hf (Y.hat_an W p).contDiffAt]; apply congr_arg; ext1 v
    obtain ⟨L,hL⟩:= Y.hat_cost i p v
    exact (congr_fun hL _).trans ((sub_eq_zero.mp ((map_sub L U W).symm.trans ((congr_fun hL _).symm.trans (hA.1 i hi v)))).trans (congr_fun hL _).symm)
  let F:= z • inputSeries q (Y.path M U) (m:=Y.stageSide p)
  have heq x : draft z (Y.path M x) q ∘ (arm G (Y.stageSide p) 1)=F+Y.eHat x p:=by
    funext i; rfl
  rw [heq,heq]
  have hf:ContDiffAt ℝ 2 F 0:= (stain_knit _ _ hp).analytic.contDiffAt.const_smul z
  have hk:ContDiffAt ℝ 2 (Y.eHat U p) 0:= (turns_analytic _ hp.width hp.two).contDiffAt
  have hS:ContDiffAt ℝ 2 (Y.eHat W p) 0:= (turns_analytic _ he.width he.two).contDiffAt
  rw [iteratedFDeriv_add_apply hf hk,iteratedFDeriv_add_apply hf hS]; apply congr_arg; ext1 v
  obtain ⟨L,hL⟩:= Y.e_cost 2 p v
  exact (congr_fun hL _).trans ((sub_eq_zero.mp ((map_sub L U W).symm.trans ((congr_fun hL _).symm.trans (hA.2 v)))).trans (congr_fun hL _).symm)
where ell (U:Cube G){σ A Λ:ℝ}(hp:(Y.path M U).Bounds q σ A Λ): ContDiffAt ℝ ω (fun x:Bid.Dir G (Y.stageSide p)=> mainTerm q (Y.path M U) (represent x)) 0 := Work.F02.mainTerm_contDiffAt hp fun i=> (Work.F03.represent_smooth (n:=Y.stageSide p) i).contDiffAt
lemma realign {R: PathData G}{α:ℝ}{ρ:GainWire a m}(h:Bubble V Q Z N m R (sat D V N m t) α ρ) (hp:t-u∈ (label D m).seam)(he: SatPath V N m (sat D V N m u)): Bubble V Q Z N m R (sat D V N m u) α ρ:=by
  refine ⟨h.earns,he,fun j F=>?_⟩; obtain ⟨hr,hk,hh,hc,hf⟩:= h.steps j F
  let Y (i:ℕ)(hi:i≤4):= same_classical_path _ _ _ _ _ hp h.lives.bound he.bound α j i hi
  have hv:=(Y 2 (by decide)).2
  refine ⟨hr,hk,hh,fun i hi p=> ⟨(hc i hi p).1,(Y i hi).1.2.1,(hc i hi p).2.2.trans (Y i hi).1.2.2⟩,hf.branch,hf.born,hv.2.1,?_⟩
  intro p l v x y hx hy w; erw [← hv.2.2]; exact hf.wave_price p l v x y hx hy
end seams
end YM.UVExtension.Reward

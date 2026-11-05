import YM.Planned.PRIMARY_INTEGRAL_295.Belays
import YM.Planned.PRIMARY_INTEGRAL_295.Xacts
/-!
Exact at any orientation row even on magnetic negative bonds. F0 & D
sqrt channel aligned. Uses prior pre-L Ringlet affiliation/kinetic
in another comparison, here compute first order under B_FUND schedulers.
At exact rows a=0,v generated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Sextants
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place Next.Fluctuations
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform Honey Drupes Density Mowing Festoons Work.F03 Xacts
open Bid (pulled bills Sworn stretch)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {c f : Side} {S:StepData c f}
variable (K:Core G S) (s: Signed) (v:Dir G c)

lemma birth (u:ℝ) : K.seek s (u • v) 0 = represent (u • pulled (Little.Core.rustic (S:=S) v) s) :=by
    rw [← represent_pulled s]; unfold seek menu; rw [Bosom.reaches_zero,show collect G (0:Dir G f) =0 from rfl,Work.G07.at_zero_increment]
    apply congr_arg (pull s 0); funext i; rw [←Precision.exp_copy _ _, Work.F03.represent_link]; unfold Little.Core.rustic
    change _*1=G.lieExp (u • linearCopy S.ratio (collect G v) ((Work.E03.poleEquiv f).symm (pole i))); rw [show (Work.E03.poleEquiv f).symm (pole i)=i from Equiv.symm_apply_apply ..]; rw [mul_one]; unfold linearCopy; split
    · simp
    rfl

lemma births (u:ℝ)(a:Temps G f): K.seek s 0 (u • a)=represent (u • pulled (K.reachable a) s) :=by
    unfold seek; rw [← represent_pulled, show K.reachable (u•a)=u•K.reachable a from map_smul (Bosom.placed K) u a]
    unfold menu; rw [link_one,replica_one]; rfl

omit v in
lemma seek_zero: K.seek s 0 0=1 := by have he:=birth K s (0:Dir G _) 0; simpa using he

lemma venue_value (u:ℝ): venue s (u•v)=represent (u•pulled v s):= represent_pulled ..
omit v in
lemma venue_zero (c : Side) (G:Gauge): venue s (0:Dir G c)=1 := by have he:= venue_value s (0:Dir G c) 0; simpa using he

def bowed : Temps G f →L[ℝ] Dir G f:= LinearMap.toContinuousLinearMap
    ({ toFun := fun a=> pulled ((Bosom.placed K) a) s
       map_add' a b:= by simp only [map_add,combined]
       map_smul' t a:= by rw [map_smul,scaled]; rfl }:Temps G f →ₗ[ℝ] Dir G f)
omit v in
lemma spout (a:Temps G f): K.seek s 0 a=represent (bowed K s a):= by have he:=births K s 1 a; simp only [one_smul] at he; exact he

section F0Exact
variable {Q:Teller G}(h:Teller.Funds Q S K.tube)
include h
omit s v in
lemma bottom_t: K.F0 0=0:= by
   ext i; obtain ⟨⟨s,i|i⟩,k⟩:=i
   · change ballast * (K.fro s 0 i) k=0
     unfold fro Tube.Xf Tube.Xn; rw [seek_zero,venue_zero]; simp only [Xacts.plotted_zero, Pressure.zip, map_zero, Finset.sum_const_zero, sub_self,mul_eq_zero]; simp
   change ballast * (K.crock s 0 i) k=0
   unfold crock Little.Core.target Tube.Xn Tube.Z; rw [seek_zero,Push.settled S (h.knobs.symm ▸ h.kernel),venue_zero];
   simp only [Xacts.plotted_zero,Pressure.zip,map_zero,Finset.sum_const_zero,Pi.one_apply, inv_one,mul_one,G.curvature_unit,smul_zero,sub_zero]; simp

-- y V log path mixture.T_JP. Need Φ continuous in Hal and smooth-on-contours.
def xcope (u:ℝ) := K.tube.Xn K.R (venue s (u • v))
def xcopeLin:= cutX K.tube.low K.tube.down (pulled v s) S.patch.L.val K.R
lemma receipts (i:Twin c): HasDerivAt (fun u:ℝ=> xcope K s v u i) (xcopeLin K s v i) 0 ∧ xcope K s v 0 i=0:=by
   unfold xcope xcopeLin; rw [zero_smul,venue_zero]; constructor
   · simp_rw [venue_value]; obtain ⟨T,T',hA,hB⟩:= h.feeds; apply flat_der
     exacts [show K.tube.down.Bounds K.tube.low Q.below.width Q.below.paths T' from h.low.symm ▸ hB,S.patch.L.property]
   exact Xacts.plotted_zero ..

omit h s v K in
private lemma zipper {E:Type} [Fintype E] {L: E→ ℝ→ Pay G} {X:ℝ→E→G.Color} {b:E→G.Color} (h:∀ i,DifferentiableAt ℝ (L i) 0) (he:∀ i,HasDerivAt (fun x=>X x i) (b i) 0 ∧ X 0 i=0):
   HasDerivAt (fun u:ℝ=>∑ i:E, L i u (X u i)) (∑ i:E, L i 0 (b i)) 0:= by
   apply HasDerivAt.fun_sum; intro i _; obtain ⟨hf,hg⟩:=he i; have hh:= (h i).hasDerivAt.clm_apply hf
   rwa [hg,map_zero, zero_add] at hh

lemma reachable_cost :
    let a := fun x:ℝ=> venue s (x • v); let R:=K.R
    (∀ i j,DifferentiableAt ℝ (fun x=>K.tube.Φ R (a x) i j) 0) ∧ ∀ i j,DifferentiableAt ℝ (fun x=>K.tube.Φ' R (a x) i j) 0 :=by
   obtain ⟨r,C,hC,h₁,h₂,hv,hS⟩:= Belays.days G 1 S.patch Q.bind
   obtain ⟨A,hA,hB⟩:= Belays.territories G 1 S.patch Q C (zero_le_one.trans hC) h₁
   obtain ⟨hf,hc⟩:= hB c f S K rfl h s 0 (hS c f S K h.knobs rfl 0 (by rw [norm_zero]; exact h₂.le)) -- explicit setup
   intro a R; let L (x:ℝ):= x•v
   have hd : DifferentiableAt ℝ L 0:= by unfold L; fun_prop
   constructor
   · intro i j; obtain ⟨b,hb,he⟩:=hf i; refine DifferentiableAt.comp (g:=fun p:Dir G c=>K.tube.Φ R (venue s p) i j) _ ?_ hd; rw [zero_smul]; exact (he j).analytic.differentiableAt (by simp)
   intro i j; obtain ⟨b,hb,he⟩:=hc i; refine DifferentiableAt.comp (g:=fun p:Dir G c=>K.tube.Φ' R (venue s p) i j) _ ?_ hd; rw [zero_smul]; exact (he j).analytic.differentiableAt (by simp)

def sheerF (p:Twin f):= cutX K.tube.high K.tube.up (pulled (rustic (S:=S) v) s) 1 K.R p - Pressure.zip (K.tube.Φ K.R 1) (xcopeLin K s v) p
def sheerI (p:Bond c):= zLin S (pulled (rustic (S:=S) v) s) (pulled v s) p - Pressure.zip (K.tube.Φ' K.R 1) (xcopeLin K s v) p

lemma sheer (q:Twin f⊕Bond c): HasDerivAt (fun u:ℝ=> K.bind (s,q) (u•v)) (Sum.elim (sheerF K s v) (sheerI K s v) q) 0:=by
   let z:= xcope K s v; let η:= fun u:ℝ=>venue s (u•v)
   have he:η 0=1:=by unfold η; rw [zero_smul,venue_zero]
   obtain ⟨hf,hc⟩:=reachable_cost K s v h
   let a:= pulled (rustic (S:=S) v) s; let b:=pulled v s
   let k:=Push.SectorMeasure.Oriented.choice s K.k
   rcases q with q|q
   · have hg:= zipper (X:=z) (fun j=>hf q j) (receipts K s v h); simp only [zero_smul, venue_zero] at hg
     have ha: HasDerivAt (fun u:ℝ=> K.tube.Xf K.R (K.seek s (u•v) 0) q) (cutX K.tube.high K.tube.up a 1 K.R q) 0:=by
       obtain ⟨T,T',hA,hB⟩:= h.feeds; simp_rw [birth]; apply flat_der
       exacts [show K.tube.up.Bounds K.tube.high Q.top.width Q.top.paths T from h.high.symm ▸ hA,one_pos]
     exact ha.sub hg
   have hg:= zipper (X:=z) (fun j=>hc q j) (receipts K s v h); simp only [zero_smul, venue_zero] at hg
   have ht:= zTest_deriv (S:=S) (G:=G) (h.knobs.symm ▸ h.kernel) k q (a,b)
   have hx: HasDerivAt (fun u:ℝ=> Tube.Z S (K.target s (u • v) 0) (venue s (u • v)) q) (zLin S a b q) 0:= by unfold Little.Core.target; simp_rw [birth,venue_value]; exact ht
   exact hx.sub hg

lemma token (i:Twin f⊕Bond c)(j:G.ColorIndex):
     fderiv ℝ (fun v=> K.F0 v ((s,i),j)) 0 v=ballast*((Sum.elim (sheerF K s v) (sheerI K s v) i) j):=by
   let L(y:Dir G c):= K.F0 y ((s,i),j); let F_ := Sum.elim (sheerF K s v) (sheerI K s v) i
   let E:=EuclideanSpace.proj (𝕜:=ℝ) j
   have hx: HasDerivAt (fun u:ℝ=> L (u • v)) (ballast * F_ j) 0:= by
     exact ((E.hasFDerivAt (x:= _)).comp_hasDerivAt _ (sheer K s v h i)).const_smul ballast
   apply (Push.side (x:=v) L ?_).unique hx
   obtain ⟨r,C,hr,hC,hp⟩:= Belays.showcase G 1 S.patch Q
   exact (hp c f S K rfl h 0 (by rw [norm_zero]; exact hr.le) _).analytic.differentiableAt (by simp)
end F0Exact
end YM.Planned.PrimaryIntegral295.Sextants

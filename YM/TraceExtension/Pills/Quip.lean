import YM.TraceExtension.Fen.Prune
import YM.TraceExtension.Pi.Liken
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {X:Type}
abbrev Wo(G:Gauge):=Atom G 2
abbrev Cards(G:Gauge):= Fin 2→G.ColorIndex
abbrev Mur(G:Gauge)(n:Side):=Site n× Signed
open Work.F03
def blatch (p:Wo G)(U:Config G n):= ∑ s:Signed,∑ x:Site n,p.unmasked (pull s 0 U) x
def paper(L:Finset X)(P:X→Wo G)(U:Config G n):= VerifiedReset.factor * ∑ j∈L, blatch (P j) U
lemma rollate (U:Config G n)(o:Site n)(x:Wo G): x.unmasked (Lattice.translate o U) 0=x.unmasked U o:=by
    simp only [Atom.unmasked,Slot.atSite,Push.Local.expand_translate,zero_add]
lemma fromR (R:Rep G n)(L:Finset ℕ): piste R loopF L=paper L R.path.loop:=by
    funext U; unfold paper piste blatch; simp only[Finset.sum_apply]; rw[sum_comm, mul_sum]; apply sum_congr rfl fun i _=>?_; unfold seatP fer; rw [←Finset.mul_sum]; apply congr_arg (VerifiedReset.factor*·)
    rw [Fintype.sum_prod_type]; refine sum_congr rfl fun s _=> ?_; rw [← Equiv.sum_comp s.actEquiv.toEquiv]; refine sum_congr rfl fun x _=>?_ ; rw [show (ul R.path R.clip (loopF i) (0:Site n))=_ from rfl, show Seat.view (s,s.actEquiv.toEquiv x) U=Lattice.translate x (pull s 0 U) from roll_c x s U]; exact rollate _ _ _
variable (P:Wo G)(y:Site n)
def spunW(p:Slot)(x:Site n)(z:Link G n)(b:G.ColorIndex):= p.atSite (input G n z) x b
def eyeB (X: Link G n)(x:Site n)(p:PlaqAxes)(c:G.ColorIndex) := faceCurl (x,p) (arm G n _ X) c
def crease (i: Fin 2)(b:Cards G)(x:Link G n):= eyeB x (wrap n (P.leg i).offset+y) (P.leg i).plaq (b i)
def laceF(b:Cards G)(U V:Link G n):= P.coeff b*(crease P y 0 b U*crease P y 1 b V)
lemma beamP (i:Fin 2)(b:Cards G) :
   let f(x):=spunW (P.leg i) y x (b i); f 0=0 ∧ ContDiffAt ℝ ω f 0 ∧ ∀ z:Link G n,fderiv ℝ f 0 z= crease P y i b z:=by
   intro f; let N:=P.leg i; let L:G.Color→L[ℝ] ℝ:=EuclideanSpace.proj (b i)
   obtain ⟨D,hD,H⟩:= armsP 0 G 0 le_rfl; obtain ⟨g,hg,h⟩:=Fen.pardon G D 0 hD
   have hs:= h _ n y N N.length le_rfl (input G n) 0 (H n 0 (by simp))
   have hx: ContDiffAt ℝ ω f 0:= L.contDiff.contDiffAt.comp _ hs.analytic
   refine ⟨by unfold f spunW; rw[input_zero,atSite_path, WilsonStartup.face_one, G.curvature_unit,map_zero];rfl,hx,fun z=> HasDerivAt.unique (Push.side f (hx.differentiableAt (by simp)) z) ?_⟩
   apply (L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (slot_deriv N y (arm G n 1 z))).congr_of_eventuallyEq
   exact Eventually.of_forall (fun t=>by unfold f spunW; change L (N.atSite (represent (arm G n 1 (t • z))) y)=L (N.atSite (represent (t • arm G n 1 z)) y); rw[map_smul])
lemma shelfB: ContDiffAt ℝ ω (fun x: Link G n=> P.unmasked (input G n x) y) 0:=by
    obtain ⟨D,hD,H⟩:=armsP 0 G 0 le_rfl
    obtain ⟨g,h,hf⟩:= roundBill G D hD 0 2
    exact (hf _ n y P _ _ (H n (0:Link G n) (by simp))).analytic
lemma creased(X Y:Link G n):
    sheen (fun U=> P.unmasked U y) X Y=(∑ b,laceF P y b X Y)+(∑ b,laceF P y b Y X):=by
    let T (b:Cards G)(x:Link G n):= (crease P y 0 b x,crease P y 1 b x); let M(b:Cards G)(i:Fin 2)(x:Link G n):= spunW (P.leg i) y x (b i)
    let F(b:Cards G)(x:Link G n):=M b 0 x*M b 1 x; let S(b:Cards G):= P.coeff b • F b
    have hf(b:Cards G): (ContDiffAt ℝ ω (F b) 0):=(beamP P y 0 b).2.1.mul (beamP P y 1 b).2.1
    unfold sheen
    rw [show (fun U=> P.unmasked U y) ∘ input G n=∑ b,S b from funext (fun x=>by unfold Atom.unmasked Atom.poly; simp only [Function.comp_apply,Fin.prod_univ_two,Finset.sum_apply];rfl), iteratedFDeriv_sum_apply (u:=univ) (f:=S) (fun b _=> ((hf b).of_le (m:= (2:ℕ)) le_top).const_smul (P.coeff b)), _root_.sum_apply,← Finset.sum_add_distrib]
    apply sum_congr rfl fun b _=>?_; obtain ⟨hp,hX,hx⟩:= beamP P y 0 b; obtain ⟨hf',hY,hy⟩:= beamP P y 1 b
    unfold S; rw [iteratedFDeriv_const_smul_apply ((hf b).of_le le_top),_root_.smul_apply]; have hh:= (criss (ContinuousLinearMap.mul ℝ ℝ) (M b 0) (M b 1) hX hY hp hf').2.2 X Y
    rw [show iteratedFDeriv ℝ 2 (F b) _ _=_ from hh]; unfold laceF; rw [← hx,← hx,← hy, ← hy]; exact mul_add ..
lemma blender (s:Signed)(V U:Link G n):
    sheen (fun W=> P.unmasked (pull s 0 W) y) V U= (∑ b,laceF P y b (orderTurn s V) (orderTurn s U))+(∑ b,laceF P y b (orderTurn s U) (orderTurn s V)):=by
    rw [← creased]; unfold sheen; let T:=fun x: Link G n=>P.unmasked (input G n x) y; let L:Link G n→L[ℝ] Link G n:= (flipCoords s ℝ).toContinuousLinearMap
    rw [show ((fun U=>P.unmasked (pull s 0 U) y) ∘ input G n)=T ∘ L from funext fun x=> congr_arg (fun U=> P.unmasked U y) (flip_links s x),iter_lin_at (L:=L) ((map_zero L).symm ▸ (shelfB P y).of_le (m:=(2:ℕ)) le_top),map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]; congr 1; ext1 i; fin_cases i<;>rfl
end YM.Trace.Pills

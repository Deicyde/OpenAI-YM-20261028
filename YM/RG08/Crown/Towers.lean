import YM.RG08.Crown.Seal

/-!
# On shell top decks in their own curvature convention. Unit response rank two template;
 thermal slots don't perturb the leading chosen Hessian. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Crown
open Carrel Camera Room Cloud Glyph Function Finset MvPolynomial Filter Lattice Rudder Forms Pert.Bulk
open Wilson WilsonStartup Design Exterior Anchor Rudder.Symmetry RG
open scoped ContDiff Topology PowerSeries BigOperators Classical RealInnerProductSpace
variable {G:YM.Gauge}{P:Side}{k:ℕ}

private def center (b:TypeFace 2) : Coord (n:=k):=fun _=>(0,b)
private lemma matched {b : TypeFace 2}(i:Fin k): deposit (Anchor.compress 2 (prize G k)) i (center b)=extractAtom G (plaqEquiv.symm b) (Tensor.coeff (inK G) k 0):=by
 suffices hleg : (deposit (Anchor.compress 2 (prize G k)) i (center b)).leg = (extractAtom G (plaqEquiv.symm b) (Tensor.coeff (inK G) k 0)).leg by
    cases h:deposit (Anchor.compress 2 (prize G k)) i (center b) with
    | mk leg coeff=> cases j:extractAtom G (plaqEquiv.symm b) (Tensor.coeff (inK G) k 0) with
      | mk l c=>
        rw [h,j] at hleg
        suffices he:coeff=c by rw [he,show leg=l from hleg]
        change (Atom.mk leg coeff).coeff=(Atom.mk l c).coeff
        rw [←h,←j];funext t;rw [terminal_charge,opening,if_pos (show (∃ v, center b (k:=k)=fun _=>(0,v)) from ⟨b,rfl⟩)];rfl
 funext j
 have he:(Extra.Iteration.slot (0:Cover) (plaqEquiv.symm b)).walk=[]:=List.length_eq_zero_iff.mp (by unfold Extra.Iteration.slot;rw [Extra.Iteration.route_length,sub_self];simp [Laurent.size])
 change Extra.Iteration.slot 0 _ = Design.plaquette (plaqEquiv.symm b)
 dsimp [Extra.Iteration.slot] at he
 cases e: route 0 (0:Cover) (Extra.Iteration.tie 0)
 · simp [Extra.Iteration.slot,Design.plaquette,center]
 simp at e

private def grains (k:ℕ)(p:PlaqAxes) : Coord (n:=k):= center (plaqEquiv p)
private lemma colored [NeZero k] {G:YM.Gauge}(p:PlaqAxes)(i:Fin k):deposit (Anchor.compress 2 (prize G k)) i (grains k p)= extractAtom G p (Tensor.coeff (inK G) k 0):=by unfold grains;rw [matched,plaqEquiv.symm_apply_apply]
private lemma plants (i:Fin k):Injective (grains k):=by
 intro a b h;exact plaqEquiv.injective (congrArg (fun x=> (x i).2) h)

def carduse (G:YM.Gauge)(k n:ℕ)(i:Fin k)(o:Fin n)(v:Cmix P G.ColorIndex 1→ℝ):ℝ := reading (Isles.pour (Carrel.completed (prize G k) i n) o) v

-- rank-author may contribute throughout K≥k via nonlinearity of slots.
lemma matinee (k n:ℕ)(i:Fin k)(o:Fin n)(v:Cmix P G.ColorIndex 1→ℝ):
 carduse G k n i o v=(Fintype.card Signed:ℝ)⁻¹ * ∑ s:Signed,∑ p:PlaqAxes,∑ y:Site P, eval (treated s v) (tap n (flask (sheet G y p k))):=by
 letI h : NeZero k:=⟨Nat.ne_of_gt i.pos⟩
 obtain ⟨D,hD,H⟩:=earned (σ:=1) G k i
 unfold carduse;rw [hatch (F:=prize G k) _ (Anchor.expand_path (grown_y _)) H zero_lt_one (by linarith)];congr 1;apply Finset.sum_congr rfl;intro s _
 let F(x:Coord (n:=k)):=∑ y:Site P,MvPolynomial.eval (treated s v) (tap n (flask (showAtom (deposit (compress 2 (prize G k)) i x) y)))
 have he : Function.support F⊆Set.range (grains k):=by
    intro x hx;by_contra! hh
    have hm : (deposit (compress 2 (prize G k)) i x).coeff=0:=by
       funext j;rw [terminal_charge,opening,if_neg (by rintro ⟨a,ha⟩;apply hh;exact ⟨plaqEquiv.symm a,by simp [ha,grains];rfl⟩)];rfl
    apply hx
    have hz(y: Site P):showAtom (deposit (compress 2 (prize G k)) i x) y=0:=by funext j;simp only [showAtom,Atom.unmasked,Atom.poly,hm,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
    unfold F;simp [hz,flask_zero,tap]
 change (∑' b,F b)=_
 rw [← Injective.tsum_eq (plants i) he,tsum_fintype];apply Finset.sum_congr rfl;intro p _;unfold F;rw [colored];rfl

-- polynomial reading commutation. `hatch` is R-valued; want actual flask power from pull. Rather
-- use diagonal∑ directly, via theorem glimpses & eventual linearity, or prove linear interpolation.
end YM.RG08.Crown

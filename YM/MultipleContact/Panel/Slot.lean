import YM.MultipleContact.Panel.Blade
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Taylor subtraction in a split linear slot of a joint test (no tensor factorization). -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.MultipleContact.Panel
open Set Function Filter MeasureTheory
open scoped ContDiff Classical BigOperators
variable (X V:Type*)[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup V][InnerProductSpace ℝ V]
structure Lens where
       read : X →L[ℝ] V
       put : V →L[ℝ] X
       take (y:V): read (put y)=y
namespace Lens
variable {X V}(p:Lens X V)
def off : X →L[ℝ] X:=.id ℝ X - p.put.comp p.read
def lay (x:X)(y:V):=p.put y+p.off x
@[simp] lemma read_off(x:X):p.read (p.off x)=0:=by simp [off,p.take]
@[simp] lemma lay_read (x:X):p.lay x (p.read x)=x:=by change p.put (p.read x)+(x-p.put (p.read x))=x; abel
@[simp] lemma read_lay (x:X)(y:V):p.read (p.lay x y)=y:=by simp [lay,p.take]
def slice (x:X)(f:X→ℂ)(y:V):= f (p.lay x y)
lemma slice_smooth (x:X){f:X→ℂ}(hf:ContDiff ℝ ∞ f):ContDiff ℝ ∞ (p.slice x f):=hf.comp (p.put.contDiff.add contDiff_const)
lemma slice_deriv (n:ℕ)(x:X){f:X→ℂ}(hf:ContDiff ℝ ∞ f)(m:Fin n→V)(y:V):iteratedFDeriv ℝ n (p.slice x f) y m=iteratedFDeriv ℝ n f (p.lay x y) (fun k=>p.put (m k)):=by
      change iteratedFDeriv ℝ n ((fun a=> f (a+p.off x))∘p.put) y m = _
      have hd : ContDiff ℝ ∞ (fun (y:X)=>f (y+p.off x)):=hf.comp (contDiff_id.add contDiff_const)
      rw [p.put.iteratedFDeriv_comp_right hd y (show (n:ℕ∞ω)≤∞ by exact_mod_cast (show (n:ℕ∞)≤⊤ by simp))]
      change iteratedFDeriv ℝ n (fun a=>f (a+p.off x)) (p.put y) (fun k=>p.put (m k))=_
      rw [iteratedFDeriv_comp_add_right]; rfl

def atom (i:ℕ)(f:X→ℂ)(x:X):= (i.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ i f (p.off x) (fun _=>p.put (p.read x))
def atoms (m:ℕ)(f:X→ℂ)(x:X):=∑k∈Finset.range (m+1),p.atom k f x
def trim (s:ℝ)(m:ℕ)(f:X→ℂ)(x:X):= f x-cutoff s (p.read x) • p.atoms m f x
lemma trim_on (s:ℝ)(m:ℕ){f:X→ℂ}(hf:ContDiff ℝ ∞ f)(x:X):p.trim s m f x=diff s (.some m) (p.slice x f) (p.read x):=by
      unfold trim diff; simp only [slice,lay_read]
      have hk(k):p.atom k f x=coeff k (p.slice x f) (p.read x):=by rw [atom,coeff,p.slice_deriv k x hf,lay,map_zero,zero_add]
      rw [atoms,polyJet]; congr 2; exact Finset.sum_congr rfl fun k _=>hk k
lemma atom_smooth (i){f:X→ℂ}(hf:ContDiff ℝ ∞ f):ContDiff ℝ ∞ (p.atom i f):=by
      have hv : ContDiff ℝ ∞ (iteratedFDeriv ℝ i f):=hf.iteratedFDeriv_right (by change ((⊤:ℕ∞):WithTop ℕ∞) + ((i:ℕ∞):WithTop ℕ∞) ≤ ∞; rw [← WithTop.coe_add]; simp)
      let E:=ContinuousMultilinearMap ℝ (fun _:Fin i=>X) ℂ; let I:= ContinuousLinearMap.id ℝ E
      have hu:ContDiff ℝ ∞ (fun (y:E × (Fin i → X))=>(I y.1) y.2):=contDiff_iff_contDiffAt.mpr (fun x=> I.cpolynomialAt_uncurry_of_multilinear.contDiffAt)
      have hp:(ContDiff ℝ ∞ (fun (y:X)=>fun (_:Fin i) =>p.put (p.read y))):=contDiff_pi.mpr (fun i=>p.put.contDiff.comp p.read.contDiff)
      exact (hu.comp ((hv.comp p.off.contDiff).prodMk hp)).const_smul _
lemma trim_smooth (m s){f:X→ℂ}(hf:ContDiff ℝ ∞ f):ContDiff ℝ ∞ (p.trim s m f):=hf.sub (((cutoff_smooth s).comp p.read.contDiff).smul (.sum (fun i _=>p.atom_smooth i hf)))

lemma atom_blades (i)(f:X→ℂ)(x:X) (hf:ContDiff ℝ ∞ f):p.atom i f x=(i.factorial:ℝ)⁻¹ • blades (List.ofFn (fun _:Fin i=>p.put (p.read x))) f (p.off x):=by rw [blades_eval hf]; rfl
omit p [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma blade_rail (x v:X){f g:X→ℂ}(hf:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ g x)(h:∀t:ℝ,f (x+t • v)=g (x+t • v)):blade v f x=blade v g x:=by
      let G:=fun (t:ℝ)=>x+t • v
      have h0:G 0=x:=by unfold G; simp
      have hG:HasDerivAt G v (0:ℝ):=by
         have h' := HasDerivAt.smul_const (hasDerivAt_id (x:=(0:ℝ))) v
         exact (one_smul ℝ v) ▸ h'.const_add x
      suffices hh : HasDerivAt (f∘G) (blade v f x) 0 ∧ HasDerivAt (g∘G) (blade v g x) 0 by rw [← hh.1.deriv, ← hh.2.deriv,show f∘G=g∘G from funext h]
      have m(u:X→ℂ)(hu:DifferentiableAt ℝ u x):HasDerivAt (u∘G) (blade v u x) 0:= ((h0.symm ▸ hu : DifferentiableAt ℝ u (G 0)).hasFDerivAt.comp_hasDerivAt 0 hG).congr_deriv (by rw [h0]; rfl) -- maybe theorem name
      exact ⟨m _ hf,m _ hg⟩
lemma read_rail (x v:X)(hv:p.read v=0)(t:ℝ): p.read (x + t • v)=p.read x:=by rw [map_add,map_smul,hv,smul_zero,add_zero]
lemma blade_complement (v:X) (hv:p.read v=0)(f:X→ℂ)(hf:ContDiff ℝ ∞ f):blade v (f ∘ p.off)=blade v f ∘ p.off:=by
      funext x
      have he:p.off v=v:=by change v-(p.put (p.read v))=v; rw [hv,map_zero,sub_zero]
      rw [blade, fderiv_comp _ (hf.differentiable (by simp) _) (p.off.differentiableAt), ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,he];rfl
lemma blade_atom (v:X)(hv:p.read v=0)(f:X→ ℂ)(hf:ContDiff ℝ ∞ f)(i:ℕ): blade v (p.atom i f) = p.atom i (blade v f):=by
      funext x; let L:=List.ofFn (fun _:Fin i=>p.put (p.read x)); let root:=blades L f
      let y:= (i.factorial:ℝ)⁻¹; let h:= root ∘ p.off
      have hs:ContDiff ℝ ∞ h:= (blades_smooth hf ..).comp p.off.contDiff
      have eq:blade v (p.atom i f) x = blade v (y • h) x:=blade_rail x v ((atom_smooth p i hf).differentiable (by simp) _) ((hs.const_smul y).differentiable (by simp) _) (fun t=>by rw [p.atom_blades i f _ hf,p.read_rail x v hv t]; rfl)
      rw [eq,blade, fderiv_const_smul (hs.differentiable (by simp) x)]
      change y • blade v h x =_
      change y • blade v (root∘p.off) x =_
      rw [p.blade_complement v hv root (blades_smooth hf L)] -- root delta
      rw [p.atom_blades i _ _ (blade_smooth hf v)]
      change y • blade v (blades L f) (p.off x)= y • blades L (blade v f) (p.off x)
      rw [blades_pin hf]
lemma blade_atoms (v:X)(hv:p.read v=0)(f:X→ℂ)(hf:ContDiff ℝ ∞ f)(i:ℕ):blade v (p.atoms i f)=p.atoms i (blade v f):=by funext x; unfold atoms; change blades [v] (p.atoms i f) x=_; change blades [v] (fun y=>∑k∈Finset.range (i+1),p.atom k f y) x = _; rw [blades_sum (Finset.range (i+1)) _ (fun k=>p.atom_smooth k hf)];exact Finset.sum_congr rfl (fun k _=>congr_fun (p.blade_atom v hv f hf k) x)
lemma blade_trim (v:X)(hv:p.read v=0)(f:X→ℂ)(hf:ContDiff ℝ ∞ f)(i:ℕ)(s:ℝ): blade v (p.trim s i f) = p.trim s i (blade v f):=by
      funext x; let y:=cutoff s (p.read x); let h:=p.atoms i f
      have hs:ContDiff ℝ ∞ h:= ContDiff.sum (fun k _=>p.atom_smooth k hf)
      have hsub:ContDiff ℝ ∞ (f - y • h) := hf.sub (hs.const_smul y)
      rw [blade_rail x v ((p.trim_smooth i s hf).differentiable (by simp) _) (g:=f-y • h) (hsub.differentiable (by simp) _) (fun t=>by rw [trim,p.read_rail x v hv t];rfl)]
      change blades [v] (f-y•h) x =_
      rw [blades_sub hf (g:=y • h) (hs.const_smul y),blades_smul y hs]
      exact congr_arg (fun r=>blade v f x-y • r x) (p.blade_atoms v hv f hf i) -- definally
lemma blades_trim (v:List X)(hv:∀t∈v,p.read t=0)(f:X→ℂ)(hf:ContDiff ℝ ∞ f)(i:ℕ)(s:ℝ): blades v (p.trim s i f) = p.trim s i (blades v f):=by
     induction v with
     |nil=>rfl
     |cons x w IH=>rw [List.forall_mem_cons] at hv; simp only [blades]; rw [IH hv.2]; exact p.blade_trim x hv.1 _ (blades_smooth hf w) i s
end Lens
end YM.MultipleContact.Panel

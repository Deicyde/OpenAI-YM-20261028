import YM.TraceExtension.Weir.Symph
import YM.TraceExtension.Soot.Coffer
import YM.MergeProof.Fondue
import YM.Push.LOCAL_SPLITTING.Atoms
/-!
 # In-place certified books.Exponential proxies at same order
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shunt
open RG Wilson Lattice Source Labels Finset Push.Local Next.Foundations MergeProof Planned.GuardedAtom Guard Extra.Histories Filter Function
open MeasureTheory
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side} (T:SectionData F)(H:Hol G)(R:Rep G n){Zκ:ℝ}
abbrev Film(G:Gauge)(n:Side):=Config G n→ℂ
-- F activation acts ultimately at root.Base.Frames.S lifts.
structure AtomD(X:Coefficient F n)(g:Film G n)(t q e:ℝ):Prop where
   shape : X.Format 0 H R
   charge : ∃ a, F.coeffSize X.x+a≤ q∧ X.remBound 0 R (Real.sqrt t) a
   pays : ∃ f,Attainment R.p 0 f e∧profile R.activities X.forced=hook R.activities R.p.threshold f
   birth : ∀ U,X.density 0 T R U= (R.eval U:ℂ)*g U
include R
lemma voyage (K : Keeper R.p R.activities)(P:Support n)(Z:Film G n){σ C Λ δ v κ c b:ℝ}(hp:R.Lawful σ C Λ δ v)(hv:0<v)(ht:P.card*v≤1)(hx:Readable H T R.p n κ)(hz:R.p.Regular P Z)(hl:R.p.supBounds (0:Site n) P Z c) (hf:T.footprint (0:Site n) ⊆ P) (hm:∀ U,‖Z U‖≤b):
   let r:= atomPrice H F κ * c; let t:= b+r
   let e:= readPrice H F*c + R.p.mass P r+ 2*(P.card:ℝ)*Real.sqrt v*R.p.mass P t
   ∃ Y:Coefficient F n,AtomD T H R Y Z v e (reservedMass R.p P t) ∧ Y.x=weighted H F 0 P R.p.threshold Z:=by
    intro r t e; let F':= residual H T 0 P R.p.threshold Z; let f':= rebate H T 0 P R.p.threshold Z; have ht': joint T 0 P=P:= union_eq_left.mpr hf
    obtain ⟨h₀,h₁,h₂,h₃⟩:= convert_atom 0 hx hz; have h₂:= (reads_null_iff ..).mp h₂
    have hQ:= charge_atom 0 hx hz hl; have hp':=ht' ▸ h₃
    let b':= Z- masked R.p.threshold P Z+ f'; have h : Attaches R.p.threshold P b':= ⟨fun U V hu hh=> congr_arg₂ (· + ·) (congr_arg₂ (·-·) (hz.sites _ _ hu) (uses_mask _ hz.sites _ _ hu hh)) ((show Attaches R.p.threshold P f' from ht' ▸ h₃).1 U V hu hh),fun i U=>congr_arg₂ (· + ·) (congr_arg₂ (· - ·) (hz.symmetry ..) (invariant_mask hz.symmetry R.p.threshold P i U)) (h₃.symmetry ..),((hz.borel.sub (masked_measurable _ _ _ hz.borel)).add h₃.borel),fun U H=>by change Z U- _+f' U=0; rw [masked_eq _ _ _ _ H,show f' U=0 from h₃.healthy_zero U (ht'.symm ▸ H)]; ring ⟩
    let X:= weighted H F 0 P R.p.threshold Z
    have hC(U):‖b' U‖≤t:=by change ‖(Z U- masked _ _ _ U)+f' U‖≤b+r; apply (norm_add_le ..).trans (add_le_add ?_ (hQ.2 U)); by_cases hy:Healthy R.p.threshold P U; rw [masked_eq _ _ _ _ hy,sub_self,norm_zero]; exact (norm_nonneg _).trans (hm 1); rw [masked_ne _ _ _ _ hy,sub_zero]; exact hm U
    have hs(U): Extra.Histories.part T 0 R U X + masked R.p.threshold P F' U+b' U=Z U:=by
        change _ +_ +(Z U-_+ (masked _ _ _ _ - Push.Local.primary T 0 R.p.threshold X U - masked _ (joint T _ _) _ U))= Z U; rw[ht']; change _+masked _ _ F' _ +(Z U- _+( masked _ _ Z _ - Extra.Histories.part T 0 R U X - masked _ _ F' _))=Z U; ring
    obtain ⟨Y,hY,hg,hp'',he,f,hf,hG⟩:= platter R K H T hp hv ht (show R.p.Regular P F' from ht' ▸ h₀) (show R.p.supBounds 0 P F' r from ht' ▸ hQ.1) h₂.1 (fun h=>h₂.2 (ht'.symm ▸ h)) (ht' ▸ h₁) h ((norm_nonneg _).trans (hC 1)) hC hs; refine ⟨Y,⟨hg,⟨_,?_,he⟩,⟨f,hf,hG⟩,hp''⟩,hY⟩
    rw [hY]; have h:=weighted_bound H F 0 hz hx.order hx.power hl; refine (add_le_add_left h _).trans_eq ?_; unfold e r; ring
end YM.Trace.Shunt

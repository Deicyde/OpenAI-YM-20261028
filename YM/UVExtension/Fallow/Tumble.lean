import YM.UVExtension.Orchard.Muesli
import YM.UVExtension.Fallow.Sundown
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D) (hF:Fridge C u ζ) {d N p:ℕ}

abbrev Rested (C : Family G){X:Type*}[Norm X](f:ℕ→X):= Slow C Extraction.Order.full fun i=> f i.1
namespace Rested
variable {X Y:Type*}[Norm X] {w:ℕ→X}
lemma money (h:Rested C w){ε:ℝ}(he:0<ε)(p:ℕ): ∀ᶠ N in atTop, ‖w N‖ ≤ flight C ε (N,p):=by
   have he:= h _ he; rw [Extraction.Order.fused] at he; exact he.exists.choose_spec
lemma levies (p:ℕ) (h:∀ ε:ℝ,0<ε→∀ᶠ N in atTop,‖w N‖≤ flight C ε (N,p)): Rested C w:=by intro ε he; rw [Extraction.Order.fused]; exact Eventually.of_forall fun _=> h ε he
lemma paid (h:Spar w): Rested C w:=by
   obtain ⟨c,hc⟩:=h; exact (Slow.const c).reduce ((cutoff_grows _).eventually (hc.mono fun n hn=> hn.trans (Real.le_norm_self _)))
lemma sinking {w:ℕ→ℝ}(h:Rested C w){ε:ℝ}(he:0<ε){x:ℝ}(hx:0<x)(p:ℕ): ∀ᶠ N in atTop,w N * flight C (-ε) (N,p) ≤ x:=by
   let F:=Extraction.Order.full; have h' : ∀ᶠ i in F.fuse, w i.1 * flight C (-ε) i ≤ x:= (h.sink (half_lt_self he)|>.and ((flight_lands (C:=C) (f:=Extraction.Order.full) (half_pos he)).eventually_le_const hx)).mono fun i hi=> hi.1.trans hi.2
   rw [Order.fused] at h'; exact h'.exists.choose_spec
end Rested
-- Use Bleak(top weight) directly across projection. C terminal fixed.
def Bleak (p:ℕ)(x:ℕ→ C.label d): Prop:= Rested C fun i=> (C.factory d i p).terminal.symm (x i)
namespace Bleak
lemma physical (H : Vintage.YM.Family.Makes C)(p:ℕ){x:ℕ→ C.label d}(h:Spar x):Bleak p x:=by
   unfold Bleak; refine Rested.levies p (fun ε he=> ?_); obtain ⟨r,hr⟩:= h; filter_upwards [Vintage.YM.Work.D01.terminal_ball C H d r _ he,hr] with i hi hx; exact hi _ (x i) hx
lemma scalar {x:ℕ→ C.label d}{v:ℕ→ℂ}(h:Bleak p x)(hw:Spar v): Bleak p fun i=> v i • x i:=by
   unfold Bleak Rested; simp_rw [map_smul]; exact Slow.smul (Rested.paid hw) h
lemma sub {x y:ℕ→ C.label d}(h: Bleak p x)(p':Bleak p y): Bleak p (x-y):=by
   unfold Bleak Rested; simp_rw [Pi.sub_apply,map_sub,sub_eq_add_neg]; apply Slow.add h; exact Slow.reduce p' (Eventually.of_forall fun i=> (norm_neg ..).le)
end Bleak

def garment (F:Stem C p)(d:ℕ):= ∃ X : Finset Cover, 0∈X∧∃ c b:ℕ→ℝ, Rested C c∧Rested C b∧∀ᶠ N in atTop,∀ o:Site (C.S.side N p), clothed (C.path.levels.budget N) (regional X o) o (weight C d N • bloom (F N) o) (c N) (b N)
include H hG
lemma cloak (x: ℕ→ C.label d)(p:ℕ)(h:Bleak p x): garment (thor x p) d:=by
  let T:= C.localSection d; let F:= C.labels.level d; let P i:= C.path.levels.budget i; let X i:= (C.factory d i p).terminal.symm (x i)
  obtain ⟨b,hb,hB⟩:= offmask C d; let c i:= (C.path.levels.params i).columns * F.coeffSize (X i); let f i:= b * F.coeffSize (F.scaled ((P i).threshold⁻¹) (X i))
  have hz: Rested C (fun i=> f i):= (Slow.const (C:=C) b).mul (scaled_slow (fun i=> X i.1) h hG); have hv : Rested C (fun i=> c i):=columns_slow.mul (coords_slow (fun i=> X i.1) h)
  refine ⟨T.stencil,(Vintage.YM.Family.Makes.sections H d).anchored,c,f,hv,hz,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d)] with i hi o; rw [blossoms,charged]; have hm:= Vintage.YM.Push.RelayDifference.section_bounds C d i p H hi o (X i)
  exact ⟨hm.1,hm.2,mul_nonneg (zero_le_one.trans hb) (coeff_pos ..),hB _ _ _⟩
omit H hG
lemma cloakNext (F: Stem C p)(ht:garment F d)(hp: RelayDifference.shiftCosts C Extraction.Order.full) (a: Axis) : garment (Fallow.entry F a) (d+1):=by
  obtain ⟨X,hX,c,b,hc,hb,H⟩:=ht; let D := X.image (fun x=> x+Lattice.step a) ∪ X; let V N:= RelayDifference.jump (C.path.levels.budget N)
  refine ⟨D,Finset.mem_union_right _ hX,fun N=> V N*c N+c N,fun i=>b i+b i,((Slow.mul hp hc).add hc), hb.add hb,?_⟩
  filter_upwards [H] with N hi o; obtain ⟨hx,hA,hB,hU⟩:= hi o; obtain ⟨hy,hY,hQ,hv⟩:= hi (o+Lattice.step a)
  have hD : regional X (o+Lattice.step a) ⊆ regional D o := by
      rintro x hx; obtain ⟨y,hy,rfl⟩:= Finset.mem_image.mp hx; exact Finset.mem_image.mpr ⟨_,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy), by rw [map_add,wrap_step]; abel⟩
  have hD' : regional X o⊆ regional D o:= Finset.image_subset_image Finset.subset_union_right; have hm:= regular_larger hy hD; have hs:=regular_larger hx hD'; have ha : separation (o+Lattice.step a) o≤ 1:=by rw [separation,add_comm,add_sub_cancel_right]; exact pdist_step _
  have he:(C.S.a N:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos _|>.ne'); unfold RelayDifference.weight; rw [Fallow.pushed,pow_succ,smul_smul, mul_assoc,mul_inv_cancel₀ he,mul_one,smul_sub]
  exact ⟨regular_sub hm hs,bound_sub hm hs (bound_larger (dir_shift _ _ _ _ _ ha hY) hD) (bound_larger hA hD'), add_nonneg hQ hB, fun U=> (norm_sub_le ..).trans (add_le_add (hv U) (hU U))⟩
end YM.UVExtension.Fallow

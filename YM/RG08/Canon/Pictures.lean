import YM.RG08.Canon.Layer
import YM.Next.STATIONARY.Shape.Scaled
/-! # Tunable/Genuine path jets matching by real wave transport
 Payment only for winding. No inference from paths at distinct infrared
 representations. Uses all real phases glyph (relative positive rank and
 factorial). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {r : ℕ} {k : ℕ → Side} {F : Pot G (r+1)} {U : ℕ→Pot G (r+1)}
variable {Q P : Picture G r} {V H : ∀ i,Link G (k i) → ℝ} {η A : ℝ} {δ : ℕ→ℝ}

-- gallery displacement price
private lemma sticks {α : Type} [Fintype α][DecidableEq α] {F : Shift α → ℝ} (x : Phase α) (hx : star x=x) (h : Width η A F)(hp:0<η) :
   Summable (fun i=> mode x i • (F i:ℂ)) := by apply Summable.of_norm; simpa [norm_smul,mode_real x _ hx] using! (h.summable hp.le).norm
lemma gallery_mend (h : Mending U F) : ∃ δ : ℕ→ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ i, 0 ≤ δ i ∧ ∀ b j x, star x=x → ‖gallery (U i) b j x-gallery F b j x‖ ≤ δ i := by
  obtain ⟨w,A,hE,HR⟩:=h.1; obtain ⟨s,f,hs,hL,T⟩:=h.2
  refine ⟨f,hL,fun v=>⟨(T v).nonneg,fun b j x hx=>?_⟩⟩
  have he : gallery (U v-F) b j x=gallery (U v) b j x-gallery F b j x := by
    obtain ⟨w,C,hp,H⟩:=h.ever v; let L:=fun i=>(j i,b i)
    have hg:= (sticks _ hx (finger_charge H L) hp).tsum_sub (sticks _ hx (finger_charge HR L) hE)
    unfold gallery aria Laurent.read; simp only [Pi.sub_apply,Complex.ofReal_sub, smul_sub]; exact hg
  rw [← he]; have ht:= gallery_funds (T v) hs b j; exact ht.2 x (ht.in_range hx)
-- Harvest under discrepancy aperture
lemma absorbed (h: ∀ i, aperture (cents (k i)*δ i) (H i) (V i) r) (hd:Tendsto δ atTop (𝓝 0))(he:Mending U F) (hz:∀ i,Tunable (U i))(hg:∀ i,Tensor.coeff (V i) _ 0=recital (U i) (k i)) :
   ∃ d:ℕ→ℝ,Tendsto d atTop (𝓝 0) ∧ ∀ i, Recorded (gallery F) (H i) (cents (k i)*d i) := by
  obtain ⟨p,hp,hv⟩:= gallery_mend he; refine ⟨δ+p,by simpa using! hd.add hp,fun i x b y=>?_⟩
  -- use three terms
  let z:= noteAt (V i) (r+1) (glyph x b y); let N:= cents (k i)
  have hZ : z= _:= (record_exact ..).1 (gallery_marks (hz i) (hg i)) x b y -- col
  change ‖_ - collected _ _ _ _‖ ≤ _
  rw [Pi.add_apply,_root_.mul_add]; refine (norm_sub_le_norm_sub_add_norm_sub (noteAt (H i) _ _) z _).trans (add_le_add (h i x b y) ?_)
  let n : ℝ:=cents (k i); have hn : 0≤n:=(cents_pos (m:=k i)).le -- implicit
  rw [hZ,collected,collected]; split_ifs
  · rw [← mul_sub,norm_mul, show ‖(↑(Fintype.card (Site (k i))):ℂ)‖=n from by unfold n cents; simp]
    exact mul_le_mul_of_nonneg_left ((hv i).2 b y _ (out_real _)) hn
  rw [sub_self,norm_zero]; exact mul_nonneg hn (hv i).1

lemma floors_mark (h: ∀ i, aperture (cents (k i)*δ i) (H i) (V i) r) (hd:Tendsto δ atTop (𝓝 0))(he:Mending U F) (hz:∀ i,Tunable (U i))(hg:∀ i,Tensor.coeff (V i) _ 0=recital (U i) (k i))
   (hp:∀ i j, Firm η A (Q i j))(hm:∀ i,Recorded Q (H i) 0)(hQ:Tendsto (fun i=>(k i).val) atTop atTop) :
      ∀ i j p, Q i j (axes p)=gallery F i j (axes p) := by
  obtain ⟨d,hL,hD⟩:= absorbed h hd he hz hg
  obtain ⟨w,C,hp',hw⟩:=he.1
  intro i j p; obtain ⟨a,b,H',hZ⟩:=fleet k hQ (axes p) (axes_real p)
  apply tendsto_nhds_unique (harvest hp (F:=H) (ε:=fun _=>0) (fun i=> by rw [mul_zero]; exact hm i) tendsto_const_nhds p a b H' hZ i j); exact harvest (gallery_funds hw hp') hD hL p a b H' hZ i j
lemma floors_equal {m:Side} {f:Link G m→ℝ} (h : ∀ i j p, Q i j (axes p)=gallery F i j (axes p))(hf : Tunable F) (he:Recorded Q f 0) : Tensor.coeff f (r+1) 0= recital F m := by -- m f
  let g:= stanza F m
  have hp : Recorded (gallery F) g 0 := gallery_marks hf (hf.pick m) -- namespace
  have hx : aperture 0 f g r := by
     intro p i b; dsimp only; rw [(record_exact ..).1 he,(record_exact ..).1 hp,collected,collected]; split_ifs
     · have hx:=out_real p; rw [← axes_of_real hx, h]; simp
     simp
  rw [← hf.pick m, Tensor.coeff, Tensor.coeff, aperture_eq hx]
end YM.RG08.Canon

import YM.UVExtension.Fallow.Yolk
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth Metric
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D) {d N p:ℕ}
open Extra.Histories Motion Next.Extract Harvest
-- deteriorating price contradiction. even unknown P projection.
lemma infinite {V:Type}[Norm V]{x:ℕ→ V}(h:¬ Spar x): ∃ t:ℕ→ℕ,Tendsto t atTop atTop∧ Tendsto (fun i=> ‖x (t i)‖) atTop atTop:=by
    have hx(b:ℝ)(m:ℕ):∃ i:ℕ,m ≤ i∧ b < ‖x i‖:=by
       contrapose! h; exact ⟨b,eventually_atTop.mpr ⟨m,h⟩⟩
    choose t ht hT using fun (i:ℕ)=> hx (i:ℝ) i
    exact ⟨t,tendsto_atTop_mono (f:=id) ht tendsto_id,tendsto_atTop_mono (f:=fun i:ℕ=> ↑i) (fun i=> (hT i).le) tendsto_natCast_atTop_atTop⟩
variable {T: Cuts C d} (Y:Yards C d p T) (K: Extraction.Wcmain C) (hl: Slicing C d p)
include H Y K hl
lemma braced {x:ℕ→ C.label d}(hp:Bleak p x)(hx : ∀ i:Shot C.book,suitable C.S p i.f → Spar fun j=> snapshots i d (j,p) (x j)): Spar (fun i=> T i (x i)):=by
   let f i:= T i (x i); obtain ⟨I,b,L,hb,hI,hL,h⟩:=hl; obtain ⟨c,hc,hT⟩:= certain H Y K hI L hL hb h
   by_contra he; obtain ⟨t,ht,hM⟩:=infinite (x:=f) he
   -- scale using complement value + 1 even before thresholds
   let a (i:ℕ):ℝ:= (‖f i‖+1)⁻¹; let g (i:ℕ): ℂ:=a i; let z i:= g i • (x i-f i); let y i:= g i • f i
   have hA i : 0< a i:= by unfold a; positivity
   have hg i:‖g i‖ = a i:= by rw [show g i=(a i:ℂ) from rfl, Complex.norm_real,Real.norm_of_nonneg (hA i|>.le)]
   have hp (i:ℕ): T i (f i)=f i:= Y.changes ..
   have hr i: T i (y i)= y i:=by unfold y; rw [map_smul,hp]
   have ha (i):‖g i‖≤1:=by rw [hg]; apply inv_le_one_of_one_le₀; linarith only [norm_nonneg (f i)]
   have hy i : ‖y i‖=1-a i:=by unfold y; rw [norm_smul,hg]; unfold a; field_simp; ring
   have hz : Bleak p z :=by
      unfold z; simp_rw [smul_sub]; exact show Bleak p ((fun i=>g i • x i)-y) from Bleak.sub (Bleak.scalar ‹Bleak p x› ⟨1,Eventually.of_forall ha⟩) (Bleak.physical H p (x:=y) ⟨1,Eventually.of_forall fun i=> (hy i).trans_le (sub_le_self _ (hA i|>.le))⟩)
   have hZ(I':Shot C.book)(hq:suitable C.S p I'.f): Tendsto (fun i=> Dash.Shot.scan I' d i p (z i)) atTop (𝓝 0):= Yards.nullTest H Y K hz (Eventually.of_forall fun i=> by apply LinearMap.mem_ker.mpr; change T i (z i)=_; unfold z; rw [map_smul,map_sub,hp,show T i (x i)= f i from rfl,sub_self, smul_zero]) I' hq
   have hE:Tendsto (a ∘ t) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ hM)
   have hV:Tendsto (fun i=> ‖y (t i)‖) atTop (𝓝 1):=by simp_rw [hy]; simpa only [sub_zero] using! tendsto_const_nhds (x:=1)|>.sub hE
   let s i j:= Dash.Shot.scan j d (t i) p (C:=C)
   have hQ j (hj:j∈I):Tendsto (fun i=> ‖s i j (y (t i))‖) atTop (𝓝 (0:ℝ)):=by
       obtain ⟨u,hu⟩:=hx j (hI j hj)
       have he:Tendsto (fun i=> s i j (g (t i) • x (t i))) atTop (𝓝 0):=by
           rw [tendsto_zero_iff_norm_tendsto_zero]; simp_rw [map_smul,norm_smul,hg]; refine squeeze_zero' ?_ ?_ (show Tendsto (fun i=>a (t i)*u) atTop (𝓝 0) from by simpa only [zero_mul,Function.comp_apply] using hE.mul_const u)
           · exact Eventually.of_forall fun i=> mul_nonneg (hA _|>.le) (norm_nonneg _)
           exact (ht.eventually hu).mono fun i hi=> mul_le_mul_of_nonneg_left hi (hA _|>.le)
       let H:= he.sub ((hZ j (hI _ hj)).comp ht); rw [sub_zero] at H
       have hL:Tendsto (fun i=> s i j (y (t i))) atTop (𝓝 0):=by
          apply H.congr; intro i; change _- s i j (z _)=s i j _; rw [← map_sub]; unfold z y; rw [smul_sub,sub_sub_cancel]
       simpa using hL.norm
   have he := le_of_tendsto_of_tendsto (hV.const_mul c) (tendsto_finsetSum I fun j hj=> hQ j hj) ((ht.eventually hT).mono fun i hi=>hi _ (hr _))
   simp only [mul_one,Finset.sum_const_zero] at he; exact hc.not_ge he
omit Y
include hG h B
-- main vet.
lemma vetted (ht:Harvest.Harrow C u ζ) (F:Stem C p)(hp:Pasted F)(hC:∀ᶠ i in atTop,Continuous (F i))(he:garment F d)(hy:∀ I:Shot C.book,suitable C.S p I.f→ Spar (smear I F)): Wealth C F:=by
   obtain ⟨T,hT⟩:= Yards.bedroll hG H B h ht d p
   obtain ⟨x,hx,hA⟩:= socket hG H B h ht.lab F hp he hC
   let v i:= T i (x i)
   have hn: Spar v:=by
      apply braced H hT K hl hx
      intro i hS
      let z:= thor x p; let f j:= smear i F j - smear i (F-z) j
      have hp':Spar f:=by
         let l:=smear i (F-z); have hz:Tendsto (fun i=>-l i) atTop (𝓝 0):=by simpa using (faded H K i hS hA).neg
         apply Spar.plus (hy _ hS) (Spar.sturdy (x:=fun i=> -l i) ⟨0,hz⟩)
      apply hp'.same; filter_upwards [smear_sub _ _ _ hp (thorP H x)] with j hj; unfold f; rw [hj,sub_sub_cancel, scanning]
   let z:= x-v; have hz:Bleak p z := hx.sub (Bleak.physical H p hn)
   obtain ⟨W,hW,hV⟩:=hT.signal z hz (Eventually.of_forall (fun i=> by apply LinearMap.mem_ker.mpr; change T i (_- _)=0; rw [map_sub,hT.changes]; exact sub_self _)) -- hT v rewrite
   let Z:= thor x p; let Z':= thor v p; let D:= F-Z; let K':=thor z p; let V':= Z'+(D+(K'-W))
   refine ⟨hp,V', (thorC H K _ hn).plus ((hA.plus hV H).crude) H,?_⟩
   have he:F-V'= W:=by unfold V'; unfold D K'; rw [show z=x-v from rfl,flour']; unfold Z Z'; abel
   exact he.symm ▸ hW
end YM.UVExtension.Fallow

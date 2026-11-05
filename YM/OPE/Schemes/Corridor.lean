import YM.OPE.Interpolate.Education
/-!
# Main layer estimate on arbitrary points

Including power-separated exterior scales and near/far collisions. The result
with b=0 includes subpower distances to the center in the exact coefficient
cost. There is no condition that the number of tiles remains bounded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set Lattice RG Wilson MergeProof Ribbons Accent Source PhysicalNext.Repeat.Legato Next.Extract Next.UVStress Bid Prescription
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S){I J L : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{φ:Filter L}[φ.NeBot] {T : L→ℝ} {x v u a b c d y z : ℝ} {k m j: L→ℕ} (g:I→ C.book.Token) (r:J→ C.book.Token) {X:L→ I→ E4}{Y:L→J→ E4} {q q':ℕ}
variable {M} {E : Dash.Bin M} {t} {H} (Base' : Base C F M t E S H)
set_option quotPrecheck false
local notation "Λ" => U.sector.derivatives
variable {R:Prescription U.sector.derivatives}(hR:R.Coherent)(w : Mode U.sector.derivatives)
variable (hT:Tendsto T φ atTop)(hx: Corridor φ T x X)(ha:0<x)
variable (h:Org.Grill C F)
include hT hx ha h
lemma coefficient_rough : RateLE φ T (fun i=> R.ope w (X i) g 0) (x*sigma g):=by
    unfold ope; refine RateLE.sum hT (fun i hi=> ?_); refine ((RateLE.const ((R.sheet w) i) hT).mul ((viewer_alt U h g i.letter hT (fun _=>none) hx.managed (bearing_lifetime hT i).1 (director_space hT hx.room (bearing_lifetime hT i).2 ha) le_rfl ha.le).mono (b:=(x*sigma g)) (by ring_nf; rfl))).mono ?_ |>.congr ?_
    · rw [zero_add]
    filter_upwards [epoch_space hT hx.managed hx.room ha i] with k hi; simp only [reading, sub_zero,if_pos hi,unselected_view]
variable (i₀:I)(hG:G.Simple){W r' D}(L':Package C W r' D)
include i₀ hG L' Base' hR
private lemma commonC (hk:Height C.S φ T k b)(hm:Height C.S φ T m a)(hj:Height C.S φ T j d)(hb:0<b)(ho:b<a)(hd:a<x)(hw:x<d): RateLE φ T (fun i=> R.ope w (X i) g 0) (tax g a d-w.fst*a):=by
    let z:=4*(Fintype.card I:ℝ)*(d-a)-w.fst*a; let F(i:L) (u:I→C.book.Token) (x:I→ E4):= R.ope w x u 0; have hh(p:I→C.book.Token): tax p a d - w.fst*a=d*sigma p+z:=by unfold tax z; ring
    rw [hh]; refine interpolated hT hj F Λ hw (c:=0) (fun p x hx=>?_ ) (fun p x hg hx=>?_ ) (fun p x hx=>?_ ) g hx
    · exact (coefficient_rough U p w hT hx ha h (R:=R)).mono (show _ ≤ _+0 from by rw [add_zero])
    · exact hh _ ▸ grid_coeff U p Base' hR hT hG L' h i₀ hk hm hj hb ho hd hw hx.room hx.managed (Eventually.of_forall hg) w
    filter_upwards [cadence_coeff U p w hT hx ha (R:=R)] with i hi using ⟨hi.works,hi.slopes⟩

/-- Cost of every needle, from the same readout of the true product, on
all approaching configurations in a positive layer. -/
lemma common_rate : RateLE φ T (fun i=> R.ope w (X i) g 0) (( (sigma g:ℝ)-w.fst)*x):=by
    intro r hr; let f a:= tax g (x-a) (x+a) - w.fst*(x-a); have hK: f 0 < r:= by unfold f tax; linarith only [hr]
    have he: ContinuousAt f 0:= by unfold f tax; fun_prop
    obtain ⟨ε,hε,hw,hx'⟩ := ((show ∀ᶠ i:ℝ in 𝓝[>] 0,0 < i from self_mem_nhdsWithin).and ((eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds ha)).and (he.tendsto.eventually (gt_mem_nhds hK)|>.filter_mono nhdsWithin_le_nhds))).exists; have hv:0<x-ε:= sub_pos.mpr hw; let a:= (x-ε); have hp:= C.path.levels.fits.mesh
    obtain ⟨k,hk⟩:= found hT hp (show 0≤a/2 from (half_pos hv).le); obtain ⟨m,hm⟩:= found hT hp hv.le; obtain ⟨j,hj⟩:= found hT hp (show 0 ≤ x+ε by positivity); apply commonC U g Base' hR w hT hx ha h i₀ hG L' hk hm hj (half_pos hv) (by unfold a; linarith) (by linarith only [hε]) (by linarith) r hx'
local notation "σ" => sigma r
variable (s:L→ Viewers U) (hV:Intervals φ T y (centerless L) Y)(hp: Kept φ T u Y)(ht:0≤y)(hl:y≤u)(hy:y<x)
local notation "S'" => fun i=>spectator U (s i)
local notation "z0"=> centerless (U:=E4) L
local notation "life"=> ((sigma r:ℝ)*u)
include hV hp ht hl hy
omit i₀ hG L' Base' hR in
lemma raw : RateLE φ T (fun i=> observe (S' i) (beside (X i) (Y i)) (beside g r)) (x*sigma g+life):=by
    have hc:=director_space hT hx.room hV hy; rw [mul_comm x]; rcases le_total u x with ho|ho
    · exact viewer_alt U h g r hT s hx.managed hp (hc.mono hl) (ht.trans hl) ho
    exact viewer_cost U h g r hT s hx.managed hp (hc.mono hy.le) ha.le ho

local notation "X'"=> (fun i v (x:I→E4)=> observe (S' i) (beside x (Y i)) (beside v r))
private lemma commonT (hk:Height C.S φ T k b)(hm:Height C.S φ T m a)(hj:Height C.S φ T j d)(hb:y<b)(ho:b<a)(hd:a<x)(hw:x<d)(N:ℕ): RateLE φ T (fun i=> X' i g (X i)-R.truncated (S' i) N (X i) g 0 (Y i) r) (tax g a d-(N+1:ℝ)*(a-y)+life):=by
    let z:=4*(Fintype.card I:ℝ)*(d-a)-(N+1:ℝ)*(a-y)+life
    let p':= life + N*y; let f (i:L) (v:I→C.book.Token)(x:I→ E4):= X' i v x-R.truncated (S' i) N x v 0 (Y i) r
    have hf(g:I→ C.book.Token): tax g a d -(N+1:ℝ)*(a-y)+life=d*sigma g+z:=by unfold tax z; ring
    rw [hf]; refine interpolated hT hj f Λ hw (c:=p') (fun p x hx=>?_ ) (fun p x hg hx=>?_ ) (fun p x hx=>?_ ) g hx
    · refine ((raw U p r hT hx ha h s hV hp ht hl hy).mono ?_ ).sub ?_ hT
      · unfold p'; linarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) ht]
      unfold Prescription.truncated; apply RateLE.sum hT; intro k hk; have ht' := (show (k.fst:ℝ) ≤ N by exact_mod_cast ((full_bands ..).1 hk)); refine ((coefficient_rough (R:=R) U p k hT hx ha h).mul (cloudRead U r hT h s hV hp ht hl k)).mono ?_; unfold p'; linarith only [mul_le_mul_of_nonneg_right ht' ht]
    · exact hf p ▸ grid_remainder U p r Base' hR hT hG L' h i₀ hk hm hj (ht.trans_lt hb) ho hd hw hx.room hx.managed (Eventually.of_forall hg) s hV hp ht hl hb N
    exact (cadence_total (R:=R) U p r hT hx ha s hV hp hy N).mono (fun i h=>⟨h.works,h.slopes⟩)

/-- All points, one projection convention. Uniform power-separated exterior
strengthening included; mixed labels and joints of other clusters pay here. -/
lemma early_rate (N:ℕ): RateLE φ T (fun i=> X' i g (X i)-R.truncated (S' i) N (X i) g 0 (Y i) r) ((sigma g:ℝ)*x-(N+1:ℝ)*(x-y)+life):=by
    intro a ha'; let f a:= tax g (x-a) (x+a) - (N+1:ℝ)*(x-a-y)+life; have hK:f 0<a:=by unfold f tax; linarith only [ha']
    have he:ContinuousAt f 0:=by unfold f tax; fun_prop
    obtain ⟨ε,hε,hw,hx'⟩:= ((show ∀ᶠ i:ℝ in 𝓝[>] 0, 0 < i from self_mem_nhdsWithin).and ((eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (show 0<x-y from sub_pos.mpr hy))).and (he.tendsto.eventually (gt_mem_nhds hK)|>.filter_mono nhdsWithin_le_nhds))).exists
    have hv:y<x-ε:=by linarith only [hw]
    obtain ⟨b,hb,hB⟩:= exists_between hv; have H:= C.path.levels.fits.mesh
    obtain ⟨k,hk⟩:= found hT H (ht.trans hb.le); obtain ⟨m,hm⟩:= found hT H (ht.trans hv.le); obtain ⟨j,hj⟩:= found hT H (show 0≤ x+ε by positivity); apply commonT U g r Base' hR hT hx ha h i₀ hG L' s hV hp ht hl hy hk hm hj hb hB (by linarith) (by linarith) N a hx'
end YM.OPE

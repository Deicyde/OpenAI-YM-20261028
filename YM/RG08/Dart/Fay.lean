import YM.RG08.Dart.Path
/-! # Real unmasked sum analytic, exact at fixed period. Terms use actual analytic dressing from Atom. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter Work.F02
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295 Work.F03
open scoped Topology BigOperators Real ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {r k i:ℕ}{G:Gauge}{m:Side}{R σ C:ℝ} {V : Rooted ℝ (Loc G 2) r}
-- invariant aggregate holds. Real g+guard on any tests Rooted stencil. exact p. shape expansion bounds

def shore_at (p:Site m)(V:Rooted ℝ (Loc G 2) r)(X:Config G m):= ∑' i, V i*(actionP i|>.unmasked X p)
def rise_a (p:Site m)(V:Rooted ℝ (Loc G 2) r):= shore_at p V ∘ input G m
private def pupil (G:Gauge)(r:ℕ)(W:Beads (Loc G 2) r)(x: Config G m)(p:Site m):=(actionP W).unmasked x p
lemma amber_at (q: Site m) (V: Rooted ℝ (Loc G 2) r)(X: Link G m): rise_a q V X=∑' i,V i * localAtom (aTerm (actionP i)) q X:= rfl
lemma rise_t (h:Quire.Lit V σ C)(he:0<σ)(p:Site m): AnalyticAt ℝ (rise_a p V) 0 ∧ ∀ k, stitch (butter V k) m p=Tensor.coeff (rise_a p V) k 0 := by
    obtain ⟨R,hR,H⟩:= shot_ready G he; let F:= rise_a p V; let g i:= localAtom (aTerm (actionP (G:=G) (r:=r) i)) p
    choose f hf hz Hf using fun i: Beads (Loc G 2) r=> H r (actionP i) m p
    let K(i):= ‖V i‖*((actionP i).budget σ * priceSlot G^r)
    have hK : Summable K:= by
       have hv i: (actionP (G:=G) (r:=r) i).budget σ=ling σ i*Real.exp (σ*(4*r:ℕ)):= by unfold Atom.budget; rw [budget_atom, mag_atom,one_mul,Nat.cast_add,mul_add,Real.exp_add]; rfl
       rw [show K=(fun i=> (ling σ i* ‖V i‖) * (Real.exp (σ*(4*r:ℕ)) * priceSlot G^r)) from funext fun i=>by unfold K; rw [hv]; ring]; exact h.2.1.mul_right _
    let v (i:Beads (Loc G 2) r):= ((V i:ℝ):ℂ) • f i; let Y i:= V i • g i
    have hx i: ContDiff ℂ ω (v i):= (hf i).const_smul  (Complex.ofReal (V i))
    have hh i : v i ∘ axes=Complex.ofRealCLM ∘ (Y i):= funext fun x=> by unfold v Y; change (V i:ℂ)*_= ↑(V i*g i x); rw [Complex.ofReal_mul]; exact congr_arg _ (congr_fun (Hf i) x)
    have ht :(fun z=> ∑' i,v i z) ∘ axes= Complex.ofRealCLM ∘ rise_a p V := funext fun i=>by
       unfold rise_a; change (∑' j,v j (axes i)) = ↑(∑' j,Y j i); simp_rw [show ∀ j,v j (axes i)=↑(Y j i) from fun j=> congr_fun (hh j) i]; exact (Complex.ofReal_tsum ..).symm
    have hu i y (h:y∈Metric.ball 0 R) : ‖v i y‖ ≤ K i:= by change ‖(V i:ℂ)*f i y‖ ≤ _; rw [norm_mul, Complex.norm_real]; exact mul_le_mul_of_nonneg_left (hz i _ h) (norm_nonneg _)
    have hE:= earth_cont ht (analytic_series v hR (fun i=> (hx i).differentiable (by simp)) hK hu)
    refine ⟨hE,fun k=>Tensor.ext_diag _ _ ((butter_h h he k).sym p) (Tensor.coeff_symm hE.contDiffAt) (funext fun x=>?_)⟩
    let X (i:Fin k): Link G m:= x
    have hv:= mixtape Y v hR hK hx hu hh k (axes ∘ X)
    rw [show (fun x=> ∑' i,Y i x)=F from rfl,note_real] at hv; have ht i : noteAt (Y i) k (axes∘ X)= ↑(V i* rootSong (castleP (actionP i) k) m p x):= by
       unfold Y; rw [note_bill (V i) (castle_i (actionP i) k p|>.1),_root_.smul_apply,note_real]; unfold rootSong Tensor.diagonal; rw [(castle_i ..).2,Complex.ofReal_mul]; rfl
    simp_rw [ht] at hv; let f i:= V i*rootSong (castleP (actionP i) k) m p x
    have hz: Tensor.coeff F k 0 X=∑' i,f i:= Complex.ofReal_injective (by rw [Complex.ofReal_tsum,hv.tsum_eq])
    change rootSong _ m p x= Tensor.coeff F k 0 X; rw [hz]; unfold butter; have hc:= curve_pens h he k
    rw [sew_diagonal (hc.pours _),rootSong, Tensor.diagonal,st_tub _ _ hc]; have hQ : Summable fun i=> sires V (curve k) i * rosary X p (Prod.snd i):= sum_bounded hc.of_norm (fun i=> rosary_bill X p _)
    rw [hQ.tsum_prod]; apply tsum_congr; intro i
    unfold f rootSong Tensor.diagonal; rw [stitch_apply (castle_t ..|>.pens.of_norm), ← tsum_mul_left]; exact tsum_congr fun j=> (show castleP (actionP i) _ j*V i* _ = V i * (castleP (actionP i) _ j*rosary X p j) by ring)

-- gauge and origin quantities, canonical masks only after this step
lemma stage_at (h:Quire.Lit V σ C)(he:0<σ)(X: Config G m)(z:Site m): Pens (fun i=> V i*(actionP i|>.unmasked X z)):= by
    have hp: Pens V:= Ink.pens h (ling_one he.le)
    refine Summable.of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=>?_) (hp.mul_right ((2:ℝ)^r)); rw [norm_mul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); exact (Atom.unmasked_bound ..).trans_eq (by rw [mag_atom,one_mul])
abbrev plain (p:Rims r 2)(j: Fin r):= walkSlot (plaqEquiv.symm (p j).2) (p j).1
lemma actionUn (p:Rims r 2) (q:Stationary.Ink G r)(X:Config G m) (z:Site m): (actionP (staple p q)).unmasked X z=∏ i,(plain p i|>.atSite X z) (q i):= by
   change ∑ i:Stationary.Ink G r,(Pi.single q 1 : Stationary.Ink G r→ℝ) i*∏ j,(plain p j|>.atSite X z) (i j) = _; rw [sum_eq_single_of_mem q (mem_univ q),Pi.single_eq_same,one_mul]; intro i _ hi; rw [Pi.single_eq_of_ne hi,zero_mul]
-- avoid potential unavailable G06
lemma hue_slot (s: Slot)(X:Config G m)(z:Site m)(a:Site m→G.El): s.atSite (gauge a X) z=G.adjoint (a z) (s.atSite X z):= by
   simp_rw [atSite_curvature,travel_gauge]; rw [show stop z (slotWalk s)=z from ?_, G.curvature_conjugate]
   unfold slotWalk; rw [stop_append, stop_append, square_stop,reverse_stop]
def Dapple (V:Rooted ℝ (Loc G 2) r):Prop:=∀ i:Rims r 2, (fun x=> V (staple i x))∈ paints G r
lemma shore_g (hz:Quire.Lit V σ C)(hp:0<σ)(he:Dapple V) (a:Site m→G.El)(X:Config G m) (z:Site m): shore_at z V (gauge a X)= shore_at z V X:= by
    have hh (X:Config G m): shore_at z V X=∑' i:Rims r 2, ∑ q:Stationary.Ink G r,V (staple i q)*∏ j, (plain i j|>.atSite X z) (q j):= by
       have hh:= stage_at hz hp X z; unfold shore_at; rw [← (spliceEq ..).tsum_eq (fun i=> V i*(actionP i|>.unmasked X z))]; apply Eq.trans (((Equiv.summable_iff (spliceEq G r 2)).mpr hh.of_norm).tsum_prod); apply tsum_congr; intro i; rw [tsum_fintype]; exact sum_congr rfl (fun _ _=> congr_arg (V _ * ·) (actionUn ..))
    rw [hh,hh]; apply tsum_congr; intro p; simp_rw [hue_slot]; exact he p (a z) _
end YM.RG08.Dart

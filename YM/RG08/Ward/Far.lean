import YM.RG08.Ward.Around
/-! # Tiling to replicate value on every common grid exactly.
Uses synthetic ratio to choose periodic probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m d n : Side} (g : Ratio c f) (G : Gauge)

def tiltCopy : Link G g.count →L[ℝ] Link G f := LinearMap.toContinuousLinearMap {
  toFun u i:= u (g.residue i.1,i.2),map_add' _ _:=rfl,map_smul' _ _ := rfl }
def tiltGroup (U : Config G g.count) : Config G f :=fun i=> U (g.residue i.1,i.2)
lemma tilt_yes (u : Link G g.count) : input G f (tiltCopy g G u)= tiltGroup g G (input G g.count u) := by
  funext i; obtain ⟨v,i⟩:=i; rw [ encode_link, tiltGroup, encode_link]; rfl
lemma tilt_step (i : Axis) : g.residue (step i)=step i := by
  rw [← Lattice.wrap_step f i,Ratio.residue_wrap, Lattice.wrap_step]
lemma tilt_move (s : Signed)(i : Site f) : g.residue (s.act i)=s.act (g.residue i) := by
  obtain ⟨x,rfl⟩ : ∃ x:Cover,i=wrap f x := ⟨lift i,(wrap_lift _).symm⟩ -- order subst orientation
  rw [wrap_signed, g.residue_wrap,g.residue_wrap,wrap_signed]
lemma tilt_action (U : Config G g.count) (s : Signed) : pull s 0 (tiltGroup g G U)=tiltGroup g G (pull s 0 U) := by
  funext i; obtain ⟨x,i⟩:=i; cases he : s.flip i <;> simp [rerun,tiltGroup,sendEdge,Step.used,Step.rotate,posDir,he,Lattice.affine, tilt_step, tilt_move]
lemma tilt_g (k : Site g.count → G.El) (U : Config G g.count) : tiltGroup g G (Lattice.gauge k U)= Lattice.gauge (k ∘ g.residue) (tiltGroup g G U) := by
  funext i; simp [tiltGroup,Lattice.gauge,tilt_step]

lemma tilt_near {p q : ℝ→ Link G g.count} (h : EquivalentNear p q) : EquivalentNear ((tiltCopy g G)∘p) ((tiltCopy g G)∘q) := by
  rcases h with ⟨s,h⟩|⟨k,z,h,H⟩
  · refine Or.inl ⟨s,?_⟩; simp_rw [Function.comp_apply,tilt_yes,tilt_action]; exact h.mono (fun i hi=>by rw [hi])
  refine Or.inr ⟨fun t=> (k t ∘ g.residue), z,tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mp h (g.residue i),?_⟩
  filter_upwards [H] with i hi; simp only [Function.comp_apply,tilt_yes, hi]; exact tilt_g ..

lemma tilt_test (j)(V : Pot G j) (h : Summable V) (x : Link G g.count) :
    stanza V f (tiltCopy g G x)=Fintype.card (Site c) • stanza V g.count x := by
  rw [stanza_apply _ h, stanza_apply _ h,← (Equiv.sum_comp  (Equiv.ofBijective g.assemble g.assemble_bijective)),Fintype.sum_prod_type]
  let z s := ∑' j, V j* rosary (fun _=>x) s j
  let P i := ∑' j, V j* rosary (fun _=> tiltCopy g G x) i j
  have he i u : P (g.assemble (i,u))=z u := by
    apply tsum_congr; intro j'; congr 1; apply prod_congr rfl; intro k hk; unfold silks; change x (g.residue (g.assemble _+ wrap f _),_)=x _; rw [map_add,g.residue_wrap];
    rw [show g.residue (g.assemble (i,u))=u from g.assemble_res ..]
  change ∑ i,∑ j,P (g.assemble (i,j))= _; simp_rw [he]; rw [sum_const,card_univ]
lemma tilt_opus (V : Air G) (hp : ∀ i j, Summable (V i j)) (s : Link G g.count)(t k)(Q : Pot G 2)(h : Summable Q) :
    oblige Q V k t (tiltCopy g G s)= Fintype.card (Site c) • oblige Q V k t s := by
  unfold oblige grand; simp_rw [Finset.sum_apply]; rw [smul_add,tilt_test g G _ Q h s, smul_sum,add_right_inj]
  apply sum_congr rfl; intro i _; rw [← mul_smul_comm,Finset.smul_sum]; simp_rw [← tilt_test g G _ _ (hp i _)];
lemma tilt_beacon (F : Air G) (hp : ∀ i j,Summable (F i j)) (Q : Pot G 2)(h : Summable Q)
    (he : Beacon f F Q) : Beacon g.count F Q := by
  intro i v w hv hw hx; let V := tiltCopy g G∘v; let W:=tiltCopy g G∘w
  have hs k : suitify (tiltCopy g G ∘ k)= (tiltCopy g G ∘ suitify k) := funext fun t=> Eq.symm (map_smul ..)
  have ht := he i V W ((tiltCopy g G|>.analyticAt _).comp hv) ((tiltCopy g G|>.analyticAt _).comp hw) (by unfold V W; rw [hs,hs]; exact tilt_near g G hx)
  let C := (Fintype.card (Site c):ℝ)
  rw [show (fun t=> oblige Q F i t (V t))= C • (fun t=> oblige Q F i t (v t)) from funext fun t=> by rw [Pi.smul_apply]; exact (tilt_opus g G F hp (v t) t i Q h).trans (nsmul_eq_mul ..),
      show (fun t=> oblige Q F i t (W t))= C • (fun t=> oblige Q F i t (w t)) from funext fun t=> by rw [Pi.smul_apply]; exact (tilt_opus g G F hp (w t) t i Q h).trans (nsmul_eq_mul ..)] at ht
  have hy := ht.scale C⁻¹; have hb:C≠0:= by unfold C; positivity
  rwa [inv_smul_smul₀ hb, inv_smul_smul₀ hb] at hy
end YM.RG08.Reflect

import YM.TraceExtension.Momentum
import YM.Next.BOUNDARY.Unique

/-! The Euclidean trace of the Ward-normalized stress, centered in the chosen state.
It pins a Hermitian Lorentz scalar field in the realization on these labels.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Metric Complex Mink Boundary Spectral Table
open scoped Topology Matrix.Norms.Frobenius NNReal ENNReal BigOperators InnerProductSpace

variable {G : Gauge} {L : Register G} {S T : Table L} {P : DiffPlan S} {X : Table.Rotation S} {rs : S.RealSpin}
  {J : Stress S}

def stressTrace (J : Stress S) : S.Field 4 := ∑ i, J i i

lemma stressTrace_turn (hp : Tensorial X J) (K : Ortho) : X.act 4 K (stressTrace J)=stressTrace J := by
    let f : Axis → Axis → Axis → S.Field 4 := fun a i j => (↑(K.val i a*K.val j a):ℂ) • J i j
    have he : X.act 4 K (stressTrace J)= ∑ a, ∑ i, ∑ j, f a i j := by
       rw [stressTrace,map_sum]; exact Finset.sum_congr rfl (fun a _ => hp K a a)
    have hu (i j : Axis) : (∑ a, f a i j)= (↑((1:M4) i j):ℂ) • J i j := by
       unfold f
       rw [← Finset.sum_smul,← Complex.ofReal_sum]
       congr 2
       have h : K.val*K.val.transpose=1 := by
         simpa [Matrix.star_eq_conjTranspose] using (show K.val*star K.val = 1 from K.property.2)
       rw [← h]; rfl
    rw [he, Finset.sum_comm]; change ∑ i, ∑ a, ∑ j, f a i j = ∑ i, J i i
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_comm]; simp [hu, Matrix.one_apply]

/-- Vacuum phase convention; evaluated in `T` on our original table's field representative. -/
def euclideanVEV (S T : Table L) {d : ℕ} (v : S.Field d) := S.useAt T (0:Points 1) (fun _ => ⟨d,v⟩)
lemma vev_coordinates (ht : T.Homogeneous) {d : ℕ} (v : S.Field d) (x : Points 1) :
    S.useAt T x (fun _ => ⟨d,v⟩)=euclideanVEV S T v := by
    have he := ht 1 0 (fun _ _ _ => Subsingleton.elim ..) (x 0) (fun _ => (⟨d,S.representative d v⟩ : L.Token))
    rw [show Points.across (x 0) (0:Points 1)=x by
       ext1 i; rw [Subsingleton.elim i 0]; simp] at he
    exact he

lemma vev_linear {d : ℕ} : IsLinearMap ℂ (@euclideanVEV G L S T d) := by
    let M := S.classMoment T (fun _ : Fin 1 => d) 0
    suffices he : @euclideanVEV G L S T d= M.toLinearMap (fun _ => 0) 0 from he ▸ (M.toLinearMap (fun _ => 0) 0).isLinear
    funext x; change M (fun _ => x)=M (update _ _ _); congr 1; ext1 i; rw [Subsingleton.elim i 0,update_self]

lemma vev_proj (hs : T.respects S) (ht : T.Hierarchy) {d : ℕ} (v : L.Ref d) :
    euclideanVEV S T (S.project d v)= T.read (0:Points 1) (fun _ => ⟨d,v⟩) :=
    S.at_project T ht.laws.toSymmetric hs (fun _ _ _ =>Subsingleton.elim ..) (fun _ : Fin 1 => ⟨d,v⟩)

lemma vev_unit (hs : T.respects S) (ht : T.Hierarchy) (d : ℕ) : euclideanVEV S T (S.unit d)=1 := by
    let v : Fin 0 → L.Token := Fin.elim0; rw [Table.unit,vev_proj hs ht]
    have he := ht.laws.unital (x:=0) (n:=0) (fun _ _ _ => @Subsingleton.elim (Fin 1) _ ..) d v
    rw [ht.laws.trivial] at he
    have hi : (fun _ : Fin 1 => (⟨d,L.scalar d⟩:L.Token))=Fin.cons (α:=fun _ => L.Token) (L.one d) v := by funext i; rw [Subsingleton.elim i 0]; rfl
    rw [hi]; exact he

lemma vev_conj (hs : T.respects S) (ht : T.Hierarchy) {d : ℕ} (v : S.Field d) :
    euclideanVEV S T (S.conj rs d v)=star (euclideanVEV S T v) := by
    obtain ⟨a,rfl⟩ := S.onto d v
    rw [S.conj_project,vev_proj hs ht,vev_proj hs ht]; exact ht.spin.real (fun _ _ _ => Subsingleton.elim ..) (fun _ => (⟨d,a⟩:L.Token))

def centerIn (S T : Table L) {d : ℕ} (v : S.Field d) := v - euclideanVEV S T v • S.unit d
def theta (T : Table L) (J : Stress S) : S.Field 4 := centerIn S T (stressTrace J)

lemma centerIn_vac (hs : T.respects S) (ht : T.Hierarchy) {d : ℕ} (v : S.Field d) : euclideanVEV S T (centerIn S T v)=0 := by
    unfold centerIn; rw [vev_linear.map_sub,vev_linear.map_smul,vev_unit hs ht]; simp

lemma trace_real (hp : Table.Conserved P rs J) (hs : T.respects S) (ht : T.Hierarchy) : S.conj rs 4 (theta T J)=theta T J := by
    have he : S.conj rs 4 (stressTrace J)=stressTrace J := by simp only [stressTrace,map_sum,hp.real]
    unfold theta centerIn; rw [map_sub,map_smulₛₗ,he,S.conj_unit]; rw [show starRingEnd ℂ _ = _ from (vev_conj hs ht (v:=stressTrace J) (rs:=rs)).symm, he]

lemma trace_turn (hp : Tensorial X J) (hr : X.Laws P rs) (K : Ortho) : X.act 4 K (theta T J) = theta T J := by
    unfold theta centerIn; rw [map_sub,map_smul,stressTrace_turn hp,hr.identity]

lemma trace_adj (hp : Table.Conserved P rs J) (hq : Tensorial X J) (hr : X.Laws P rs)
    (hs : T.respects S) (ht : T.Hierarchy) : S.adj rs 4 timeAxis (theta T J) = theta T J := by
    rw [Table.adj,LinearMap.comp_apply,trace_real hp hs ht, ← hr.signed,trace_turn hq hr]

lemma scalar_rail {K : Spins S} (hK : K.Descends X rs) (hr : X.Laws P rs) {d : ℕ} {v : S.Field d} (hf : ∀ i, X.act d i v=v)
    (g : Lorentz) : K.rail g (S.pin d v)= S.pin d v := by
    have one (v : S.Field d) : K.shell d 1 v = v := S.pin_inj d ((hK.ties ..).symm.trans (hK.identity _))
    have mult (a b : Lorentz) (v : S.Field d) : K.shell d (a*b) v=K.shell d a (K.shell d b v) := by
        apply S.pin_inj; simpa only [hK.ties] using hK.representation a b (S.pin d v)
    have he : g∈Bid.beamGens := by rw [(Work.A16.answer : Bid.beamGens=⊤)]; trivial
    rw [hK.ties]
    apply congr_arg
    apply Subgroup.closure_induction (p := fun b _ => K.shell d b v=v) _ (one v) _ _ he
    · rintro b (⟨s,w,rfl⟩|⟨a,u,rfl⟩)
      · rw [hK.spatial,hf]
      let U := Ray.fromAxis a
      let f t := K.shell d (U.boost t) v
      have hz (r : Ortho.Skew) : X.lie d r v=0 := by
        have he := hr.infinitesimal d r v; simp_rw [hf] at he; exact he.unique (hasDerivAt_const ..)
      let m := LinearMap.toContinuousLinearMap ((-Complex.I) • X.lie d (Ortho.plane timeAxis a.castSucc))
      have hm : m v=0 := by change (-Complex.I) • X.lie _ _ v=_; rw [hz,smul_zero]
      have hs (t : ℝ) : HasDerivAt f (m (f t)) t := by
        have hd := hK.boosts d a (f t)
        simpa only [f,m,Function.comp_def, one_smul, ← mult, ← Ray.boost_add, sub_add_cancel,U] using!
           hd.scomp_of_eq t ((hasDerivAt_id' t).sub_const t) (by simp)
      have h0 : f 0=v := by simp [f,one]
      exact congr_fun (ODE_solution_unique_univ (f:=f) (g:=fun _ => v) (s:=fun _ => univ)
        (fun (_ : ℝ) => m.lipschitz.lipschitzOnWith) (fun t => ⟨hs t, mem_univ _⟩)
        (fun t => ⟨hm.symm ▸ hasDerivAt_const t _, mem_univ _⟩) h0) u
    · intro a b _ _ ha hb; rw [mult,hb,ha]
    intro a _ ha; apply (K.shell d a).injective; rw [ha, ← mult, mul_inv_cancel, one]
end YM.TraceExtension

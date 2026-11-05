import YM.Planned.ATOM_REGULAR_ESTIMATE.Translations

/-!
Position-degree bookkeeping on **literal** continuum connection tests. One
edge ODE factored through a finite record, *because* the radial coefficients
here are a Taylor polynomial through d. Uses the already established all-time
solution and endpoint germ facts. We work component by component; no uniform
jet prices on these (unweighted) statements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Flat
open Function Tensor Lattice Wilson RG Source Labels Source.Drops Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {d k : ℕ}

def position (b : Cover) : E4 := WithLp.toLp 2 (fun i => (b i : ℝ))
lemma position_next (b : Cover) (i : Axis) : position (b+step i) = position b + basis i := by
  ext j; by_cases h : j=i <;> simp [position, h]

/-- t-power record for one link's positive traversal. -/
abbrev Rad (G : Gauge) (d : ℕ) := Fin (d+1) → G.Color

def connection (p : Rad G d) (t : ℝ) := ∑ i, t^i.val • p i
@[simp] lemma connection_zero (G : Gauge) (d : ℕ) (t : ℝ) : connection (0: Rad G d) t = 0 := by
  simp [connection]
lemma connection_smooth (p : Rad G d) (k : WithTop ℕ∞) : ContDiff ℝ k (connection p) :=
  ContDiff.sum fun _ _ => ((contDiff_id.pow _).smul contDiff_const)

def record (x : E4) (i : Axis) : Snap G d →L[ℝ] Rad G d := LinearMap.toContinuousLinearMap {
    toFun J m := ∑ j : Fin (d-1), Degree.twist ((J j).val i) (basis i) m.val x
    map_add' a b := by
      funext m
      simp [Degree.twist,Finset.sum_add_distrib]
    map_smul' t a := by
      funext m; simp [Degree.twist, Finset.smul_sum] }
lemma record_at (x : E4) (i : Axis) (J : Snap G d) (m : Fin (d+1)) :
    record x i J m = ∑ j : Fin (d-1), Degree.twist ((J j).val i) (basis i) m.val x := rfl

lemma translates (J : Snap G d) (x : E4) (i : Axis) (t : ℝ) :
    potential d (expand d J) i (x+t • basis i) = ∑ k : Fin (d-1), (J k).value i (x+t • basis i) := by
  rw [potential,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro j _; rw [expand,dif_pos j.isLt]
lemma represented (J : Snap G d) (x : E4) (i : Axis) (t : ℝ) :
    connection (record x i J) t = potential d (expand d J) i (x+t • basis i) := by
  have he (j : Fin (d-1)) : (J j).value i (x+t • basis i) =
      ∑ m : Fin (d+1), t^m.val • Degree.twist ((J j).val i) (basis i) m.val x := by
    rw [Taylor.value, Degree.twist_expansion, Fin.sum_univ_eq_sum_range (fun m => t^m • Degree.twist ((J j).val i) (basis i) m x) (d+1)]
    have h := j.isLt
    have hz m (hm : j.val+1 < m) : Degree.twist ((J j).val i) (basis i) m x=0 := Finset.sum_eq_zero
      (fun s hs => by have he : s.card=m := (Finset.mem_filter.mp hs).2; have ht := (Finset.card_le_univ s).trans_eq (Fintype.card_fin _); omega)
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m hi hv; rw [hz m (by rw [Finset.mem_range] at hv; omega), smul_zero]
  unfold connection; rw [translates]; simp_rw [record_at,Finset.smul_sum,he]; exact Finset.sum_comm

lemma record_field (J : Snap G d) (x : Cover) (i : Axis) (t : ℝ) : connection (record (position x) i J) t =
    partConnection d (expand d J) 1 (x,i) t := by rw [represented,partConnection,one_smul,one_smul]; rfl

private def path (p : Rad G d) : ℝ → G.El := (Hol.pipes (connection_smooth p 1)).choose
private lemma path_solves (p : Rad G d) : SolvesLink (path p) (connection p) :=
  (Hol.pipes (connection_smooth p 1)).choose_spec
private lemma path_end (H : Hol G) (x : Cover) (i : Axis) (J : Snap G d) :
    path (record (position x) i J)=H.flow d (expand d J) 1 (x,i) :=
  (path_solves _).unique (by rw [show connection (record (position x) i J) = _ from funext (record_field J x i)]; exact H.solves ..)

def endVal (p : Rad G d) := path p 1
lemma end_link (H : Hol G) (x : Cover) (i : Axis) (J : Snap G d) :
    endVal (record (position x) i J)=H.links d (expand d J) 1 (x,i) :=
  congr_fun (path_end H x i J) 1

lemma end_diff (G : Gauge) (d : ℕ) : AnalyticAt ℝ (G.mat ∘ (endVal (G:=G) (d:=d))) 0 ∧
    endVal (0 : Rad G d) = 1 := by
  let A : Rad G d →ₗ[ℝ] (ℝ → G.Mat) := {
    toFun p t := G.colorMat (connection p t)
    map_add' f g := funext fun t => by simp [connection, Finset.sum_add_distrib, smul_add]
    map_smul' r f := funext fun t => by
      change G.colorMat (connection (r • f) t) = r • G.colorMat _
      rw [show connection (r • f) t = r • connection f t from ?_, map_smul]
      simp only [connection,Finset.smul_sum,Pi.smul_apply,smul_comm _ r] }
  obtain ⟨hr,hx,-⟩ := Work.G02.endpointGerm A
    (fun p => G.colorMat.continuous_of_finiteDimensional.comp (connection_smooth p 0).continuous)
    (fun p t => G.mat (path p t)) (fun p => by rw [(path_solves _).1,G.mat_one])
    (fun p t => (path_solves p).2 t)
  exact ⟨hr,G.mat_injective (hx.trans G.mat_one.symm)⟩

def Lower (k : ℕ) (u : Snap G d) := ∀ i : Fin (d-1), k < i.val+2 → u i = 0
lemma degree_record {u : Snap G d} (hu : Lower k u) (i : Axis) : Degree (k-1) (fun x => record x i u) := by
  have h j : Degree (k-1) (fun x => record x i u j) := by
    rw [show (fun x => record x i u j) = ∑ l : Fin (d-1), Degree.twist ((u l).val i) (basis i) j.val from funext fun x => by rw [Finset.sum_apply, record_at]]
    refine Degree.sum Finset.univ (fun l _ => ?_)
    by_cases hk : k < l.val+2
    · rw [hu l hk,show Degree.twist (((0 : Taylor G l).val) i) (basis i) j.val = fun _ => 0 by funext; simp [Degree.twist]]
      exact Degree.const 0 _
    exact Degree.mono (Degree.twist_degree ..) (by omega)
  let z (j : Fin (d+1)) := ContinuousLinearMap.single ℝ (fun _ : Fin (d+1) => G.Color) j
  rw [show (fun x => record x i u) = ∑ j : Fin (d+1), z j ∘ (fun x => record x i u j) from funext fun x => by
    simp only [Finset.sum_apply,Function.comp]; funext j; simp [z,Finset.sum_apply,Pi.single_apply]]
  exact Degree.sum _ fun j _ => (h j).linear _
end YM.Planned.AtomRegular.Flat

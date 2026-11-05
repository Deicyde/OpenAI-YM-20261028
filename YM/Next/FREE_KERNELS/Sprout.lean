import YM.Next.FREE_KERNELS.Bank
import YM.Next.FREE_KERNELS.Strands
import YM.PREC.Stacks


/-!
# Exporting the true fine differences to the cover Cross

Residue wrap crosses into a different copy; `advanceC` includes exactly
that shift. At this point accumulate one uniform budget over all axes &
difference words through the prescribed order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision
open scoped Topology BigOperators ComplexConjugate
variable {ι α β : Type*} {j t : ℕ}

lemma market_sub {a b : Cover → ℝ} (ha : Summable fun i => ‖a i‖) (hb : Summable fun i => ‖b i‖)
    (p : Momentum) (hp : physical p) : RRead (fun i => a i-b i) p=RRead a p-RRead b p := by
  have hg (a : Cover → ℝ) (ha : Summable fun i => ‖a i‖) : Summable fun i => mode p i • (a i:ℂ) := by
    apply Summable.of_norm
    simp_rw [norm_smul,mode_real p _ hp,one_mul,Complex.norm_real]; exact ha
  unfold RRead Laurent.read; rw [← (hg a ha).tsum_sub (hg b hb)]; exact tsum_congr fun i => by simp [mul_sub]

lemma market_move (a : Cover → ℝ) (p : Momentum) (x : Cover) :
    RRead (fun i => a (i-x)) p=mode p x * RRead a p := by
  unfold RRead Laurent.read; rw [← (Equiv.addRight x).tsum_eq,← tsum_mul_left]; refine tsum_congr fun i => ?_
  change mode p (i+x) • (a ((i+x)-x):ℂ)=_
  rw [mode_shift,add_sub_cancel_right]; exact mul_right_comm .. |>.trans (by ring) -- ring after smul

lemma shift_sound (a : Cover → ℝ) (ha : Summable fun i => ‖a i‖) (x : Cover) : Summable fun i => ‖a (i-x)‖ := by
  simpa only [Function.comp_def, Equiv.coe_addRight,sub_eq_add_neg] using ((Equiv.addRight (-x)).summable_iff.mpr ha)

def carryStep {L : Side} (a : Axis) (i : Site L) : Cover := if lift i a=mid L then step a else 0
lemma cover_step {L : Side} (ho : Odd L.val) (a : Axis) (i : Site L) :
    lift (i+step a)+L.val • carryStep a i=lift i+step a := by
  let x := lift i+step a-L.val • carryStep a i
  have ht := mid_double L ho
  have he : lift (i+step a)=x := by
    apply lift_eq_iff.mpr
    refine ⟨by unfold x; rw [map_sub,joint_heads,sub_zero,map_add,wrap_step,wrap_lift],fun j => ?_⟩
    obtain ⟨h1,h2⟩ := centers_odd i ho j
    unfold x carryStep
    by_cases ha : j=a
    · subst a; split <;> rename_i hh <;> simp only [Pi.zero_apply,Pi.add_apply,Pi.sub_apply,step_apply,if_true,
        smul_zero,sub_zero,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,mul_one] <;> omega
    split <;> simp [ha,nsmul_eq_mul] <;> omega
  rw [he]; exact sub_add_cancel ..

lemma enters (f : Thread j t α β) (e : ℕ) (u : List Axis) (P : Flight j t) (r : Site P.L)
    (a : Axis) (p : Momentum) : spread f e (a :: u) P r p=
    mode p (carryStep a r) • spread f e u P (r+step a) p-spread f e u P r p := by
  unfold spread; rw [Finset.smul_sum,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
  let q := aliasAt p (i:Site P.L)
  have hh : mode p (carryStep a r)*mode q (lift (r+step a))=mode q (lift r)*mode q (step a) := by
    have hx := congr_arg (mode q) (cover_step P.odd a r)
    simp only [mode_shift, ← mode_scale,show P.L.val • q=_ from alias_scale p i,mode_phase,mode_periodic,mul_one] at hx
    rw [mul_comm]; exact hx
  have he : chip (q a)=mode q (step a)-1 := by rw [Exterior.factor]; rfl
  change _ = mode p (carryStep a r) • (mode q _ • _) - mode q _ • _
  simp only [listChip,List.map_cons,List.prod_cons,smul_smul,← sub_smul]; unfold q at *
  congr 1; rw [he]; simp only [← mul_assoc]; rw [hh]; ring

variable {f : Thread j t α β}

namespace Secured
lemma bankCost [Fintype α] [Fintype β] (h : Secured f) (hj : 4≤j) (e : ℕ)
    {u : List Axis} (hu : u.length≤j-2) : ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ P : Flight j t,
      (meshBook f e u P).strip σ (C/(P.L.val:ℝ)^(e+u.length)) := by
  let I := Σ P : Flight j t, Site P.L
  obtain ⟨σ,C,hσ,hC,H⟩ := matrix_cover (h.propels hj e hu (fun i : I => i.1) (fun i => i.2)) zone_pos (fun i _ hp x hx => h.layout e u _ _ hp x hx)
  exact ⟨σ,C,hσ,hC,fun P ⟨r,a⟩ b => by rw [div_eq_mul_inv]; exact H (⟨P,r⟩:I) a b⟩
lemma bankSafe [Fintype α] [Fintype β] (h : Secured f) (hj : 4 ≤ j) (e : ℕ) {u : List Axis} (hu : u.length≤j-2) (P : Flight j t) :
    (meshBook f e u P).safe := by
  obtain ⟨σ,C,hσ,hC,H⟩ := h.bankCost hj e hu; exact Row.rights _ _ (H _) hσ.le
lemma bankRead (h : Secured f) (hj : 4≤j) (e : ℕ)
    {u : List Axis} (hu : u.length≤j-2) (P : Flight j t) (r : Site P.L) {p : Momentum} (hp : p∈baseCube) (a : α) (b : β) :
    (meshBook f e u P).read p (r,a) b=spread f e u P r p a b := by
  let I := Σ P : Flight j t, Site P.L
  have hh := record_eq (h.propels hj e hu (fun i : I => i.1) (fun i => i.2)) zone_pos
    (⟨P,r⟩:I) (fun i _ hp x hx => h.layout e u _ _ hp x hx) (fun i p hp => h.palette e u _ _ hp) hp
  exact congr_fun (congr_fun hh _) _
lemma traverse [Fintype α] [Fintype β] (h : Secured f) (hj : 4 ≤ j) (e : ℕ) {u : List Axis} (hu : u.length≤j-2) (P : Flight j t) :
    advanceC P.L (meshBook f e [] P) u = meshBook f e u P := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have hh : u.length≤j-2 := by simpa [List.length_cons] using (Nat.le_trans (Nat.le_succ u.length) hu)
    rw [advanceC,ih hh]
    have h1 := bankSafe h hj e hu P; have h₂ := bankSafe h hj e hh P
    funext ⟨l,i⟩ m
    let t p := meshBook f e u P (p,i) m
    let k := carryStep a l; let b := l+step a
    have ht := shift_sound (t b) (h₂ _ _) k
    change (fun z => t b (z-k)-t l z)=_
    apply RRead_injective (ht.of_norm.sub (h₂ _ _).of_norm).norm (h1 _ _)
    intro p hx
    rw [market_sub ht (h₂ _ _) p hx.1, market_move]
    change mode p k * (meshBook f e u P).read p (b,i) m-(meshBook f e u P).read p (l,i) m = (meshBook f e (a::u) P).read _ _ _
    rw [h.bankRead hj e hh _ b hx,h.bankRead hj e hh _ l hx,h.bankRead hj e hu _ l hx,enters]; rfl

lemma limited_lengths (K : ℕ) : Set.Finite {l : List Axis | l.length ≤ K} := by
  induction K with
  | zero => exact (Set.finite_singleton []).subset (fun x hx => by simpa using hx)
  | succ K h =>
    let s := {l : List Axis | l.length ≤ K}
    refine ((Set.finite_singleton []).union (((Set.finite_univ (α:=Axis)).prod h).image (fun p => p.1::p.2))).subset ?_
    rintro (_|⟨a,x⟩) he
    · left; rfl
    right; exact ⟨(a,x),⟨mem_univ _, by simpa using he⟩,rfl⟩
lemma honored [Fintype α] [Fintype β] (h : Secured f) (hj : 4≤j) (e : ℕ) :
    ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ (P : Flight j t) (u : List Axis), u.length ≤ j-2 →
      (advanceC P.L (meshBook f e [] P) u).strip σ (C/(P.L.val:ℝ)^(e+u.length)) := by
  letI : Fintype {l : List Axis // l.length≤j-2} := (limited_lengths (j-2)).fintype
  obtain ⟨σ,C,hp,hC,H⟩ := staple (κ:={l : List Axis // l.length≤j-2})
    (fun l σ C => ∀ P, (meshBook f e l.val P).strip σ (C/(P.L.val:ℝ)^(e+l.val.length)))
    (fun l => bankCost h hj e l.property) (fun l _ _ _ _ hv hσ hp hC P a b =>
        (hv P a b).mono hσ (div_le_div_of_nonneg_right hC (by positivity)))
  exact ⟨σ,C,hp,hC,fun P u hu => by rw [traverse h hj e hu]; exact H ⟨u,hu⟩ _⟩
end Secured
end YM.Next.Free

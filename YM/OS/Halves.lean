import YM.Lattice.Scale
import YM.OS.Train


/-!
# The needed train estimates at integral step

width d trimmed to integral steps. Pick s maximal under point resolution & family threshold.
Then **train bound** uniform for any d' multiple, with r/2 separation/slab buffer.
No unsafe L calculation. Enough to prove only selected ball of small K/r relative s.
S separate from calendar Q: requirements tie C.S upon application.
The train hypothesis is solely S-kernels; applies without W.Motion, from roots gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Function Set Filter Analysis Word
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace
variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis} (Q : Schedule)

def At (F : ℕ) (m : ℕ) (s : ℝ) := F ≤ m ∧ Q.a m < s ∧ ∀ j, F ≤ j → j < m → s ≤ Q.a j
lemma turn (F) (r : ℝ) (hr : 0 < r) : ∃ m : ℕ, At Q F m r := by
  classical
  have hh : ∃ i, F≤ i ∧ Q.a i<r := by
    exact ((eventually_ge_atTop F).and (Q.shrinks.eventually (gt_mem_nhds hr))).exists
  let m := Nat.find hh
  obtain ⟨p,t⟩ := Nat.find_spec hh
  exact ⟨m,p,t,fun j hj h => le_of_not_gt (fun ht => h.not_ge (Nat.find_min' hh (And.intro hj ht)))⟩
lemma thickness (F : ℕ) (h : Q.Gentle) : ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ m : ℕ, At Q F m ε → r * ε^2 ≤ Q.a m := by
  obtain ⟨c,hc,h⟩ := Q.mesh_inequality h
  refine ⟨min (Q.a F) c,lt_min (Q.a_pos _) hc,fun i hi he j hj => ?_⟩
  rcases eq_or_ne j F with rfl|hx
  · exact (mul_le_of_le_one_right (le_min (Q.a_pos _).le hc.le) (pow_le_one₀ hi.le he)).trans (min_le_left ..)
  let n := j-1
  have ht := lt_of_le_of_ne hj.1 hx.symm
  have hu : j=n+1 := by dsimp only [n];omega
  apply le_trans _ (show c * (Q.a n)^2 ≤ Q.a j from by rw [hu]; exact h n)
  have hz : i ≤ Q.a n := by apply hj.2.2 n <;> omega
  gcongr; exact min_le_right ..

def Covered (e : ℝ≥0) (m : ℕ) := ∃ i : ℕ, (e:ℝ)=i*Q.a m

/-- s=a(m) maximal under r/32 at depth F. dyadic n here any, r used on RHS so C enlarged; actual separations in slab r/2. -/
def Tiled (S : Table L) (a : Axis) := ∀ D R, ∃ F : ℕ, ∃ (C : ℝ) (K : ℕ), 0<C ∧ ∀ r : ℝ, 0<r → r≤1 →
    ∀ m : ℕ, At Q F m (r/32) → ∀ (e : ℝ≥0), Covered Q e m → ∀ w : L.Word, constrained D R w → w ≠ [] →
    ∀ h : Slab a e w, buffer a (r/2) e w → QRead S (Spread.radius C K w r) h

lemma narrow {e : ℝ≥0} (w : L.Word) {r : ℝ} (hr : 0<r) {m} (h : Slab a e w) (hd : buffer a r e w)
    (hp : w≠[]) (hv : Q.a m < r/32) : ∃ d : ℝ≥0, Covered Q d m ∧ d≤e ∧
    Slab a d w ∧ buffer a (r/2) d w := by
  let s := Q.a m
  let n := ⌊(e:ℝ)/s⌋₊
  have hs := show 0<s from Q.a_pos _
  let d : ℝ≥0 := ⟨n*s,by positivity⟩
  have he : (d:ℝ) ≤ e := (le_div_iff₀ hs).1 (Nat.floor_le (by positivity))
  have H : (e:ℝ) < d+s := by
    have ht := (div_lt_iff₀ hs).1 (Nat.lt_floor_add_one ((e:ℝ)/s))
    rw [add_mul,one_mul] at ht; exact ht
  have hu i (hi : i∈w) := hd.2 i hi
  have hh i (hi : i∈w) : i.1 a ≤ (d:ℝ)- r/2 := by
    have ht := (hu i hi).2; change s<_ at hv; linarith
  refine ⟨d,⟨n,rfl⟩,he,⟨?_,h.2.1,fun i hi => lt_of_le_of_lt (hh i hi) (sub_lt_self _ (by positivity))⟩,
    ⟨fun i j hk => le_trans (by linarith) (hd.1 _ _ hk), fun i hi => ⟨(by linarith [(hd.2 i hi).1]), hh i hi⟩⟩⟩
  have hk := hh (w.head hp) (List.head_mem _)
  have he := (hu (w.head hp) (List.head_mem _)).1
  change (0:ℝ)<(d:ℝ); linarith

variable (V : Chamber S a) (h : S.Hierarchy) (H : Tiled Q S a)
include Q h H
lemma priced : ∀ D (R : ℝ), ∃ C : ℝ, ∃ K : ℕ, 0<C ∧
    ∀ w : L.Word, ∀ e, constrained D R w → ∀ hp : Slab a e w, ∀ r : ℝ, 0<r → r≤1 → buffer a r e w →
      ∃ P : V.GNS.H.Op, ‖P‖ ≤ Spread.radius C K w r ∧ ∀ x, P (V.GNS.plant x)=V.GNS.plant (entering hp x) := by
  intro D R; obtain ⟨F,C,K,hC,hf⟩ := H D R
  refine ⟨C,K,hC,fun w e hw hp i hi hr ht => ?_⟩
  cases eq_or_ne w [] with
  | inl he =>
    subst w
    refine ⟨V.flow.E e, by simpa [Spread.radius] using V.flow.shrinks e,fun x => (V.atBirth e x).symm⟩
  | inr hz =>
    obtain ⟨m,hm⟩ := turn Q F _ (by positivity : 0 < i/32)
    obtain ⟨d,hd,hq,hD,hB⟩ := narrow Q w hi hp ht hz hm.2.1
    have hh := hf i hi hr m hm d hd w hw hz hD hB
    let B := Spread.radius C K w i
    have hV : 0<B := by
      have hu : 0 < w.length := Nat.pos_of_ne_zero (fun e => hz (List.length_eq_zero_iff.mp e))
      unfold B Spread.radius; positivity
    obtain ⟨P,hP,H_⟩ := producer V hD h hh hV
    let u := e-d
    refine ⟨P.comp (V.flow.E u), (ContinuousLinearMap.opNorm_comp_le ..).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (V.flow.shrinks _)).trans hP),fun x => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← V.atBirth, H_]; congr 1
    apply Subtype.ext; change linked a _ w _ = linked a _ w _; unfold linked
    simp only [travel,raised,paths]
    rw [← add_smul,← NNReal.coe_add, tsub_add_cancel_of_le hq]

omit V Q H h in
lemma affordable {w : L.Word} {e : ℝ≥0} (h : Slab a e w) : ∃ D R, constrained D R w ∧ ∃ r : ℝ, 0<r ∧ r≤1 ∧ buffer a r e w := by
  classical
  obtain ⟨D,hD⟩ : ∃ D : ℕ, ∀ i∈w, i.2.1 ≤ D := by
    have ht := eventually_all_finset _ |>.mpr fun i (_:i∈w.toFinset) => eventually_ge_atTop i.2.1
    simpa using ht.exists
  obtain ⟨R,hR⟩ : ∃ D : ℝ, ∀ i∈w, ‖i.2.2‖ ≤ D := by
    have ht := eventually_all_finset _ |>.mpr fun i (_:i∈w.toFinset) => eventually_ge_atTop ‖i.2.2‖
    simpa using ht.exists
  refine ⟨D,R,(fun i hi => ⟨hD i hi,hR i hi⟩),?_⟩
  have he p (hp : p∈w) : ∀ᶠ r in 𝓝[>] (0:ℝ), r ≤ p.1 a ∧ p.1 a ≤ (e:ℝ)-r := by
    filter_upwards [(gt_mem_nhds (h.2.1.2 p hp)).filter_mono nhdsWithin_le_nhds,
      (gt_mem_nhds (sub_pos.mpr (h.2.2 p hp))).filter_mono nhdsWithin_le_nhds] with r hr ht
    exact ⟨hr.le,by linarith [show r<(e:ℝ)-p.1 a from ht]⟩
  have ht i j : ∀ᶠ r in 𝓝[>] (0:ℝ), i ≠ j → r ≤ cubedist (positions w i) (positions w j) := by
    by_cases he : i=j
    · exact Eventually.of_forall fun _ h => (h he).elim
    have hu := h.2.1.1
    have hf : 0<cubedist (positions w i) (positions w j) := dist_pos.mpr
      (fun p => he ((show Injective _ from hu) (WithLp.ofLp_injective _ p)))
    exact ((gt_mem_nhds hf).filter_mono nhdsWithin_le_nhds).mono fun _ hh _ => le_of_lt hh
  have hy := eventually_all_finset _ |>.mpr fun i (hp : i ∈ w.toFinset) => he i (by simpa using hp)
  obtain ⟨r,hr,hp,hH⟩ := ((eventually_all.mpr fun i => eventually_all.mpr (ht i)).and (hy.and (show ∀ᶠ i in 𝓝[>] (0:ℝ), i∈ Ioc 0 1 from Ioc_mem_nhdsGT (by norm_num)))).exists
  exact ⟨r,hH.1,hH.2,hr,by simpa using hp⟩

include V Q h H in
theorem irons : ∃ X : Spread V, X.AllCopy := by
  classical
  have hv (e : ℝ≥0) (w : L.Word) : ∃ P : V.GNS.H.Op, ∀ h : Slab a e w, ∀ x, P (V.GNS.plant x)=V.GNS.plant (entering h x) := by
    by_cases h' : Slab a e w
    swap; exact ⟨0,fun p => (h' p).elim⟩
    obtain ⟨D,R,Hd,i,hi,hQ,hF⟩ := affordable h'
    obtain ⟨C,A,hC,hv⟩ := priced Q V h H D R
    obtain ⟨P,hP,I⟩ := hv w e Hd h' i hi hQ hF
    exact ⟨P,fun _ => I⟩
  choose P hP using hv
  let X : Spread V := ⟨P,fun t => hP _ _ t⟩
  refine ⟨X,fun D R => ?_⟩
  obtain ⟨C,A,h₁,h₂⟩ := priced Q V h H D R
  refine ⟨C,A,h₁,fun w e i hw r hr hb hp => ?_⟩
  obtain ⟨T,hT,H⟩ := h₂ w e i hw r hr hb hp
  exact (V.GNS.by_bud (fun i => show X.place e w _=T (V.GNS.plant i) from (hP _ _ hw i).trans (H i).symm)) ▸ hT
end YM.OS

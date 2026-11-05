import YM.RG08.Creek.Lanes
/-! # Quantitative bills. Does not choose radius based on post data. Explicit.

Use external λ(P) for occupancy amplitudes. The nonlinear bill multiple
reads ONLY the fixed metric cost & b gifts, not input cost. At rec step use F
bill narrowed to these via external Λ incl per-step stake. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I X Z:Type} [Fintype I][DecidableEq I][Fintype X][DecidableEq X][Fintype Z][DecidableEq Z]{G:Gauge}{L:Side}{R w v A B C θ:ℝ}{a:I→ℕ}{d:I→ℝ}{T:Finset I}{e j r τ E D:ℕ}{F:Layouts I G D R}{P:Head I}{K:StripU G L}
section fees
abbrev chant_cost (G:Gauge)(L:Side)(v:ℝ)(τ:ℕ)(d:I→ℝ):ℝ:= ∑ T:Finset I,∑ r∈range (τ+1), ((Fintype.card (Site L):ℝ)^T.card * (paid_shop L T r d G v*Real.exp (4*v*T.card)))
lemma shop_pos (G:Gauge)(L:Side)(v:ℝ)(T:Finset I)(D:I→ℝ)(r:ℕ): 0 ≤ paid_shop L T r D G v:= by unfold paid_shop wand_fee; positivity
lemma chant_good (G:Gauge)(L:Side)(v:ℝ)(τ:ℕ)(d:I→ℝ):0≤chant_cost G L v τ d := sum_nonneg (fun k _=>sum_nonneg fun i _=> mul_nonneg (by positivity) (mul_nonneg (shop_pos ..) (by positivity)))
lemma sky_crest (hP:Crease P)(he: Fest w E 1 P F)(hk:∃ a:I→ℕ, Sense a F ∧ ∀ t, vanes a t+E≤τ)(hw:0<w)(hv:0<v)(hp:v ≤ L.val*w)(L': I→ℝ):
    Fest v E (chant_cost G L v τ L') P (fun x=>chancel L (signet L F x L')) := by
    intro i hi j t
    obtain ⟨a,hX,hv'⟩:=hk
    by_cases ht : j≤τ
    · apply owns_mono (chanters _ (he i hi j t) hX L' hw hv hp) le_rfl
      rw [one_mul]; refine mul_le_mul_of_nonneg_right ?_ (hP.pos t)
      let f (i:ℕ)(t:Finset I):= (Fintype.card (Site L):ℝ)^t.card * (paid_shop L t i L' G v*Real.exp (4*v*t.card)); have hx i t:0≤ f i t:= mul_nonneg (by positivity) (mul_nonneg (shop_pos ..) (by positivity))
      exact (single_le_sum (f:=fun i=> f i t) (fun i _=>hx i t) (mem_range_succ_iff.mpr ht)).trans (single_le_sum (f:=fun t: Finset I=>∑ i∈range (τ+1),f i t) (fun t _=>sum_nonneg fun i _=>hx i t) (mem_univ t))
    have hx(x): chancel L (signet L F x L') t i j=0:= not_ne_iff.mp (mt ((chStyle (sign_style hX x t)).cap i j) (by have hp:=hv' t; omega))
    simp_rw [hx]; exact owns_none t _ (mul_nonneg (chant_good ..) (hP.pos t)) _ _ _
lemma own_pole {F:Places I→Rooted (Poise T D R) X r}(h: Owns v T F A)(hC:0≤C)(hv:0<v){Q:Row X Z}(hk:Q.strip v C): Owns v T (fun x=>spring (F x) Q) (((Fintype.card Z:ℝ)^r*C^r)*A) := by
    refine ⟨fun p q he=>congr_arg (fun f: Rooted (Poise T D R) X r=> spring f Q) (h.1 p q he), mul_nonneg (by positivity) h.pos,fun i=>?_⟩
    obtain ⟨U,hu,H⟩:=h.2.2 i; refine ⟨_,fun k=> pole_price Q hk hC hv (hu k),fun i'=>?_⟩
    simpa only [Tribe,mul_left_comm ((Fintype.card Z:ℝ)^r*C^r)] using budget_scale (show 0≤(Fintype.card Z:ℝ)^r*C^r by positivity) (H i') -- type inst

abbrev arrow_cost (C:ℝ)(P:StripU G L)(i j:ℕ):= ∑ k∈range (i+1), ‖glaze P.scale j k (i-k)‖ * ((Fintype.card (Loc G 1):ℝ)^j * C^j)
abbrev arrow_all (C:ℝ)(P:StripU G L)(E τ:ℕ):= ∑ i∈range (E+1),∑ j∈range (τ+1),arrow_cost C P i j
lemma arrowz (hr:0≤C)(P:StripU G L)(i j:ℕ): 0 ≤ arrow_cost C P i j:= sum_nonneg fun k _=> mul_nonneg (norm_nonneg _) (by positivity)
lemma arrow_live (hr:0≤C)(P:StripU G L)(E τ:ℕ): 0≤ arrow_all C P E τ:= sum_nonneg fun i _=> sum_nonneg fun j _=> arrowz hr _ _ _
lemma mat_check (h:Sense a F)(hp:Fair K)(hR:1/2≤ R)(hX:∀ t,vanes a t+E ≤ τ)(hP:Crease P)(hB:0≤B)(hv:0<v)(hk:(scan K.tree).strip v B)(hU:0≤C)
    (hM: Fest v E C P (solar K a d F)) : Fest v E (arrow_all B K E τ*C) P (creekT K a d F):= by
   intro i hi j t; rw [mul_assoc]
   by_cases h:j≤τ -- shadow
   · have hh(s : ℕ)(hs:s∈range (i+1)):=own_pole (hM s (by have he:=mem_range.mp hs; omega) j t) hB hv hk
     apply owns_mono (owns_sum (U:=fun k x=> glaze K.scale j k (i-k) • spring (solar K a d F x t k j) _) (range (i+1)) (fun s hs=> owns_s (hh s hs) (glaze K.scale j s (i-s)))) le_rfl
     apply le_trans (le_of_eq (show _ = arrow_cost B K i j * (C*P t) from by unfold arrow_cost; rw [Finset.sum_mul]; exact sum_congr rfl fun i _=> (mul_assoc ..).symm))
     refine mul_le_mul_of_nonneg_right ((single_le_sum (f:=arrow_cost B K i) (fun _ _=> arrowz hB _ _ _) (mem_range_succ_iff.mpr h)).trans (single_le_sum (f:=fun i=> ∑ p∈range (τ+1),arrow_cost B K i p) (fun _ _=>sum_nonneg fun _ _=> arrowz hB _ _ _) (mem_range_succ_iff.mpr hi))) (mul_nonneg hU (hP.pos _))
   rename_i hv'
   have hh x: (creekT K a d F x t i j)=0:= not_ne_iff.mp (mt ((crest_style ?_ hp hR).cap i j) (by have hp:=hX t; omega)); swap; · exact hv'
   simp_rw [hh]; exact owns_none t _ (mul_nonneg (arrow_live hB K E τ) (mul_nonneg hU (hP.pos t))) _ _ _
-- input size stake=1

def creek_cost (K:StripU G L)(τ E:ℕ)(v θ B:ℝ)(d:I→ℝ):= let N:=windows τ E; arrow_all B K E τ *((↑(N+1:ℕ):ℝ)*resp I τ E v (chant_cost G L θ τ d) B N)
lemma lit_cost (K:StripU G L)(τ E:ℕ)(hv:0<v)(hB:0≤B)(θ:ℝ)(d:I→ℝ): 0≤creek_cost K τ E v θ B d:= mul_nonneg (arrow_live hB K ..) (mul_nonneg (Nat.cast_nonneg _) (resp_z _ _ hv hB (chant_good ..)))
lemma creek_fees (hP:Crease P)(he:Fest w E 1 P F)(h:Sense a F)(hk:∀ t,vanes a t+E≤τ)(hC: Fair K)(hR:1/2≤R)(hw:0<w)(hv:0<v)(hB:0≤B)(ht:(scan K.tree).strip v B)
   (hG:advanceFee I τ v (windows τ E)≤θ)(hL:θ≤ L.val*w)(hp:(veiled K.cv).strip θ B) (hh : ∀ i≤windows τ E,∀ j≤E,∀ k, Glow (Refrain (veiled K.cv) K.song none i j k) θ B) (b:I→ℝ):
    Fest v E (creek_cost K τ E v θ B b) P (creekT K a b F) := by
   have hx:0<θ:= hv.trans_le ((show v ≤ advanceFee I τ v (windows τ E) from by simpa only [advanceFee,pow_zero,one_mul] using advance_v I hv.le (Nat.zero_le (windows τ E)) (t:=τ)).trans hG)
   have hU(x:Places I)(t): Styled (vanes a t) (chancel L (signet L F x b) t):= chStyle (sign_style h x t)
   apply mat_check h hC hR hk hP hB hv ht (mul_nonneg (Nat.cast_nonneg _) (resp_z _ _ hv hB (chant_good ..)))
   exact noon_fees hP (by linarith) (fun x t=>(hU x t).cap) hk (fun x t=>(hU x t).tidy) (fun x=>ch_z (sign_l h hC.odds hR)) hv hG (fair_he hC) hB (chant_good ..) hp hh (sky_crest hP he ⟨a,h,hk⟩ hw hx hL b)
end fees
end YM.RG08.Creek

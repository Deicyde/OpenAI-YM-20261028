import YM.Contacts.Transport.Blend
import YM.Contacts.Solstice.Deliver
/-!
# Occurrence evidence, phase uniformity

For the mixed product, use `blend`; for any individual basis word, the cheaper cost terms using
its *own* assigned weights are true. Test any compatible placement, unselected or selected. The
identity with finite summation makes linear-testing statements immediate. Real basis (w/ unital
option) available if using, but no coordinate of it was needed by the estimates. Uniformity across
selected character labels in these particular readings is in addition to the arbitrary family allowed
in general budgets. Use the whole relative stage geometry as before. Covariance & overlap statements
before testing thus apply also to the mixed forms when all components are transformed/padded using
the indicated basis and actual weight. No claim of phase-dependent improvement on expectation.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Harvest Route Transport
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {E W V W' I J : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {k : ℕ}{G:Gauge}{C: Family G}{F:Extraction.Order}{S:Table C.book}{Z:Final C F S}
local notation "GN"=> Normal.Group k
local notation "𝔈"=> Expression Z.sector.derivatives
variable (M : Devices Z.sector.derivatives)

lemma weight_held {d:ℕ}(v : S.Field d)(t) : M.splitting.part t d v ∈ M.splitting.stratum t:= M.splitting.top_mem v
lemma unit_echo (j : Fin k)(o : Points k)(P:E→ₗᵢ[ℝ] Points k) {d : Fin k→ℕ}(t:Cells S d)
   (h : t j=S.unit (d j))(x:E)(p:SmoothTests E)(s:ℝ): action x p ((waySystem P M o d t).full P s {j})= p.val x • insertField M.basis ((P x+o) j) _ (S.unit (d j)) := by rw [System.full_single,action_tmul,← h]; rfl
lemma unit_value (Y:Points 1) (d:ℕ) (ν : Viewers Z) : readExpr M.basis (spectator Z ν) (insertField M.basis (Y 0) d (S.unit d))=1:= by
   let B:= spectator Z ν; let h:=spectate Z ν; have hf: Y∈ conf 1:= injective_of_subsingleton _; let F:Fin 1→ C.book.Token:= Fin.cons (C.book.one d) (Fin.elim0); rw [show insertField M.basis (Y 0) d (S.unit d)=tokenWord M.basis Y.ofLp F from Eq.symm (?_), read_word M.basis M.coherent _ h.laws.toSymmetric (spectate_respects Z _) (spectate_ready Z _),totalObserve,if_pos (show Function.Injective Y.ofLp from hf)];
   · change observe B _ _= _; rw [named_fin B h.laws.toSymmetric _ hf]; exact (h.laws.unital hf d Fin.elim0).trans (h.laws.trivial _ _)
   unfold tokenWord; rw [Fintype.prod_unique]; rfl

variable {M}
namespace Backdrop
variable {P:E→ₗᵢ[ℝ] Points k} {g : Normal.Group k} {Q : Pieces g}{r : Route P Q I W} {δ : ℝ}{d:J→ℕ}{θ : Backdrop S r d}

def booked (θ : Backdrop S r d) (f : V→ W) : Backdrop S (pullBank r f) d where
   values v:= θ.values (f v)
   labels j v:= θ.labels j (f v)
   still _ i _ _ hx:= θ.still _ i hx
   held j _ i _ _ hx := θ.held j _ i hx
   bounds:= ⟨θ.bounds.choose,fun i v=>θ.bounds.choose_spec i (f v)⟩
   continuous v:= θ.continuous (f v)
   known j v:= θ.known j (f v)
lemma booked_eligible (h : θ.Eligible δ) (f : V→W): (θ.booked f).Eligible δ:= ⟨h.pos, fun i j hh _ x hx=> h.sober i j hh _ x hx, fun v=> h.apart (f v), fun v=> h.border (f v)⟩
end Backdrop
variable {P:E→ₗᵢ[ℝ] Points k}
variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable {g : Normal.Group k} {d:J→ℕ} {r : Route P (root g) Unit W}{δ ε : ℝ} [Fintype J] {θ : Backdrop S r d}{q : Fin k→ℕ}{Z' : W→ Cells S q}
lemma rem_all (h : Run r)(hg:g.Nonempty) (he : θ.Eligible δ) (hm:r.Authority M q)(hx:Given Z')(A: Services C F S) {n:ℕ}(hF:sees M (clasp g hg) n r)(hε:0<ε) : ∃ L>(0:ℝ),∀ w (f:Menu k)(z:SmoothTests E)(c:ℝ), (∀ i∈ (root g).parts,(f i).slice=none) → tsupport z.val⊆ barrel r w ⁻¹' r.stage w → Jet (stairs q (root g)) univ z.val c → ∀ α:Viewers Z,
      Dust (r.windings M (θ.controlled M (clasp g hg) n false (fun _=>α)) Z' f w (normal_test r w z)) (L*c* (scale r w)^((n+1:ℝ)-arityRate q g-ε)):= by
   let V:= W×Viewers Z; let v:V→ W:=Prod.fst; let r':= pullBank r v; let h': Run r':= funext fun i=> congr_fun h i.1
   let θ':= θ.booked v
   obtain ⟨L,hL,h⟩:= rem_power hg h' (given_drops Z' v hx) (show r'.Authority M q from hm) A hε (show sees M (clasp g hg) n r' from fun i=> hF _) (Backdrop.booked_eligible he v) (α:=Prod.snd)
   refine ⟨L,hL,fun w f z c hf he ht α=>?_⟩; exact h (w,α) f z c hf he ht

lemma gathered {s B : ℝ} (hH: B≤ M.clearance (∑ i,q i+0))(ha : B∈ Ioc 0 1)(hs:0<s∧2*s≤B){o:Points k} (hQ: plane (entire k) ≤ LinearMap.range P.toLinearMap) (hf:Collapsed (entire k) o) (α : Viewers Z)(z:Cells S q)(p:SmoothTests E)(ht: HasCompactSupport p.val) (H : Services C F S) :
     Integrable (fun x=> readExpr M.basis (spectator Z α) (action x p (blend M o P s (root (entire k)) q z))) ∧
     (∫ x,readExpr M.basis (spectator Z α) (action x p (blend M o P s (root (entire k)) q z)))= ∑ j:Dimensions q, ∫ x,kernel P (entire k) M ((fun i=> M.splitting.part _ _ (z i)):Cells S (carriesN j)) α o s p x:= by
   -- ctx alignment, compact support
   let T (j:Dimensions q) : Cells S (carriesN j):= fun i=> M.splitting.part _ _ (z i)
   have he(j:Dimensions q): Integrable (kernel P (entire k) M (T j) α o s p) := by
      have h': (∑ i, (j i).val+0) ≤ ∑ i,q i+0:= by simp only [add_zero]; exact Finset.sum_le_sum fun i _=> Nat.le_of_lt_succ (j i).isLt
      let Q:=glues_total M H (T j) α hQ hf (U:=tsupport p.val) ht ha (le_trans hH (M.antitone_clearance h')) hs; obtain ⟨c,hc,hX⟩:=Q; let n:=totalTestOrder (carriesN j) (entire k); obtain ⟨V,hV,F⟩:= Normal.controls (infSmooth p) ht n -- `ht` IsCompact
      exact (hX p V (Set.Subset.refl _) (F.recover (Set.Subset.refl _))).integrated
   simp_rw [blended_image M o P s (root (entire k)),map_sum]; exact ⟨integrable_finsetSum _ fun i _=> he i, integral_finsetSum _ fun i _=> he i⟩
end YM.Contacts.Solstice

import YM.RG08.Fete.Spins
/-!
# Fk Section displayed on Pack, own gauge prices all orders & rates.
 top-level polynomial dictionary renderer. Normalization Sound ally.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fete
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Trill Exterior RG Precision
open scoped Classical ContDiff Topology BigOperators ENNReal Matrix.Norms.Frobenius ComplexConjugate
variable {G:Gauge}{d n p l e D k q:ℕ}{σ B:ℝ}{S:Finset Cover}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
variable {X:Labels.Frame G d}

-- local x_i→ scalar pin
private def pin {I:Type}(i:Tape n I)(V:NoteX):Pack n I:=fun j=> if j=i then V else 0
private lemma pin_pay {I:Type}(i:Tape n I)(V:NoteX)(L:Jetty.Loom I)(h:0<σ)(hq:purse D h V ≠⊤):∃ C:ℝ,0≤C ∧ Sings L D h (pin i V) C:=by
 refine ⟨(gems L D h (pin i V) i).toReal,ENNReal.toReal_nonneg,?_⟩;unfold Sings;rw [tsum_eq_single i,ENNReal.ofReal_toReal]
 · unfold gems;rw [pin,if_pos rfl]; exact ENNReal.mul_ne_top hq ENNReal.ofReal_ne_top
 intro j hj; rw [gems,pin,if_neg hj,purse_zero,zero_mul]
private lemma pin_flow {I:Type}(i:Tape n I)(V:NoteX)(h:Voice V):Lyrics (pin i V):=fun x=>by unfold pin;split;exact h;exact quiet

def bandF {I:Type}[Fintype I](K:I→E)(M:Flake n I)(s:Jetty.Cargo p): Pack n E:=∑ i:Tape n I,M i • pin (K ∘ i) (loot s 0)
lemma purse_jet (s:Jetty.Cargo p)(h:0<σ)(hp:p≤D):purse D h (fun v=> loot s 0 v)≠⊤:=by
 apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top (b:=ENNReal.ofReal 1) (purse_le _ _ _);intro f hf
 apply ENNReal.ofReal_le_ofReal
 let c:Jetty.Jet D:=⟨⟨p,Nat.lt_succ_of_le hp⟩,s⟩
 change |openJet c 0 f|≤(1:ℝ);exact (beam_opens D h f c 0).trans (by rw [norm_zero,mul_zero,Real.exp_zero,mul_one];exact hf)
lemma band_price {I:Type}[Fintype I](K:I→E)(M:Flake n I)(s:Jetty.Cargo p)(h:0<σ)(hp:p≤D):Lyrics (bandF K M s)∧∃ C:ℝ,0≤C ∧ Sings (stance _) D h (bandF K M s) C:=by
 choose C hC H using fun i:Tape n I=>pin_pay (K ∘ i) (fun v=> loot s 0 v) (stance (Loc G 1)) h (purse_jet _ _ hp)
 refine ⟨(Lyrics.sum univ (fun i _=> (pin_flow _ _ (voiced _)).smul _)),∑ i:Tape n I,|M i| * C i,sum_nonneg (fun i (_:i∈univ)=> mul_nonneg (abs_nonneg _) (hC _)),Sings.sum univ (fun i _=>(H i).smul _) (fun i (_:i∈univ)=>mul_nonneg (abs_nonneg _) (hC i))⟩ -- fix syntax

lemma band_lace {I:Type}[Fintype I](K:I→E)(M:Flake n I)(H:Forms.Sym M)(s:Jetty.Cargo p)(f:Pearl):Forms.Sym (fun i=>bandF K M s i f):=by
 intro e;funext x
 unfold bandF
 change (∑ i:Tape n I,M i • pin (K ∘ i) (⇑(loot s 0))) (x ∘ e) f=_
 rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]
 symm
 refine Fintype.sum_equiv (Forms.twist (I:=I) e) _ _ (fun i=>?_)
 simp_rw [Pi.smul_apply];rw [show M ((Forms.twist (I:=I) e) i)=M i from congrFun (H e) i];rw [show pin (K ∘ i) (⇑(loot s 0)) x f=pin (K ∘ twist e i) (⇑(loot s 0)) (x ∘ ⇑e) f from ?_]
 unfold pin;rw [show (K ∘ twist e i)=(K ∘ i) ∘ ⇑e from rfl];simp [show (x ∘ ⇑e=(K ∘ i) ∘ ⇑e) ↔ (x= K ∘ i) from ⟨fun P=>funext (fun j=>by simpa using congrFun P (e.symm j)),fun P=>P ▸ rfl⟩];split_ifs <;>rfl

def encore (T:SectionData X)(a:Accent X): GrainS (Ed G Cover):=fun e n=> if n=e+(X.grades a.ear).2 then bandF window (ton (astro T a.ear) n) (concert a.test.play) else 0
lemma encore_form (T:SectionData X)(a:Accent X): Skiff.Lit (X.grades a.ear).2 (encore T a):=by
 intro e n hn;unfold encore at hn;split at hn;omega;exact False.elim (hn rfl)
lemma encore_price (T:SectionData X)(a:Accent X)(hd:d≤D)(σ:ℝ)(hs:0<σ)(e n:ℕ):∃ C:ℝ,0≤C ∧ Sings (stance _) D hs (encore T a e n) C:=by
 unfold encore;split;exact (band_price _ _ _ hs (a.test.held.trans hd)).2;exact ⟨0,le_rfl,tin⟩
lemma encore_permit (T:SectionData X)(a:Accent X)(h:d≤D):Permit D (X.grades a.ear).2 (encore T a):=by
 refine ⟨encore_form T a,fun f e n=>?_,fun e n=>?_⟩
 · by_cases hn:n=e+(X.grades a.ear).2
   · unfold brook during encore;rw [if_pos hn];exact band_lace _ _ (ton_sym _ (lamp T a.ear) _) _ _ -- names
   unfold brook during encore;rw [if_neg hn];exact Forms.Sym.zero
 obtain ⟨C,hC,HC⟩:=encore_price T a h 1 zero_lt_one e n
 refine ⟨?_,1,zero_lt_one,C,hC,HC⟩; unfold encore;split;exact (band_price _ _ _ zero_lt_one a.test.held).1;exact hush
-- finite delivery formulas
lemma band_val {I:Type}[Fintype I](K:I→E)(M:Flake n I)(s:Jetty.Cargo p)(f:Pearl)(x:Tape n E): bandF K M s x f= loot s 0 f *∑ i:Tape n I,if x=K ∘ i then M i else 0:=by
 unfold bandF;rw [Finset.sum_apply,Finset.sum_apply,mul_sum];apply sum_congr rfl;intro i _; simp_rw [Pi.smul_apply];unfold pin; split <;> simp [*,mul_comm]
lemma band_pay {I:Type}[Fintype I](K:I→E)(M:Flake n I)(s:Jetty.Cargo p)(f:Pearl)(X:Tape n E→ℝ): (∑' i:Tape n E, bandF K M s i f * X i)=loot s 0 f*∑ i:Tape n I,M i * X (K ∘ i):=by
 let u(t:Tape n I)(i:Tape n E):= if i=K ∘ t then loot s 0 f * M t*X i else 0
 have he(t:Tape n I):HasSum (u t) (loot s 0 f*M t * X (K ∘ t)):=by convert! hasSum_single (f:=u t) (K ∘ t) (fun b hb=>if_neg hb) (SummationFilter.unconditional (Fin n → E)) using 1; exact (if_pos rfl).symm
 have hh(i:Tape n E): bandF K M s i f * X i=∑ t:Tape n I,u t i:=by
    rw [band_val,mul_sum,sum_mul];apply sum_congr rfl;intro t _;unfold u;split <;>simp [*]
 simp_rw [hh, (hasSum_sum (f:=u) (fun t (_:t∈(univ:Finset (Tape n I)))=>he t)).tsum_eq,mul_sum];apply sum_congr rfl; intro t _;ring
end YM.RG08.Fete

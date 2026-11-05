import YM.RG08.Wax.Birth
/-! # Real scalar theorem on extracted coefficients at each root set
Exp to logarithm in marker calculus commutes with conditioning law. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Bands Analysis Laurent Lattice Bloch Next.Free
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I X:Type} [DecidableEq I] [Fintype X] [DecidableEq X] {L: Side} {p : Option Side}{K:Row X X}{S:Canticle X}
variable {a:I→ℕ}{U:Topaz I (Screed ℝ X)}{F : Topaz I (HeatS X)}{o:Site L}
lemma gust_z (V:Screed ℝ X): gust 0 V=0:= by
   funext i k; unfold gust spoolB; simp [Finset.sum_apply,braid_none,grant_zero]
lemma borne_void (V:HeatS X): borne 0 V=0:= by funext i j; unfold borne; simp [gust_z]
lemma bloom_g (h:∀ i, Reels (vanes a i) (F i))(hf:F ∅=0)(z:Site L) :
   Bulb (pearl (Co L X)) dancing (fun i=>glee (vanes a i) z (F i)) (fun i=> glee (vanes a i) z (banner i F borne (upstart X))) := by
  let T i:=banner i F borne (upstart X); have hv i := walksR h i
  refine ⟨?_,?_,?_⟩
  · dsimp only; rw [hf]; ext1 n; ext1 k; simp [glee,large]
  · dsimp only; rw [banner_one,vanes_empty,glee_empty]
  funext i
  have ht (p)(hp:p∈partners i): Reels (vanes a i) (borne (sons F p.1) (T p.2)):= by rw [wind_cell a _ hp]; exact borne_r (Reels.sm (h _) _) (hv _)
  change (↑i.card:ℝ) • glee (vanes a i) z (T i)= _; rw [← glee_sm _ (hv i)]; change glee (vanes a i) z (sons T i)=_; rw [show sons T i=_ from banner_s (upstart X) F borne borne_void i,festival,glee_list (h:=ht)]; unfold festival
  refine sum_congr rfl fun p hp=> ?_; rw [wind_cell a _ hp]; unfold sons T; rw [tempo_b (Reels.sm (h p.1) (↑p.1.card:ℝ)) (hv _), glee_sm _ (h p.1)]

lemma time_once (k:Matrix X X ℝ)(S:Op X) (U V: Op X)(h: countT U=coda k S U)(hp : countT V=coda k S V)(he : U 0=V 0): U=V:= by
   funext n; induction n using Nat.caseStrongRecOn with
   | zero=> exact he
   | ind n ih=>
     funext j; have ht:= congr_fun (congr_fun h n) j; have he':= congr_fun (congr_fun hp n) j
     apply smul_right_injective _ (show ((↑(n+1:ℕ)):ℝ)≠0 by positivity)
     change _ • (U (n+1) j)= _ • (V (n+1) j)
     rw [Nat.cast_smul_eq_nsmul ℝ _ _,Nat.cast_smul_eq_nsmul ℝ _ _]; change countT U n j=countT V n j; rw [ht,he']
     simp only [coda, landP,rim, Pi.add_apply, ih n le_rfl]; congr 1; refine sum_congr rfl fun p hp=> ?_; rw [ih p.1 (by have he:=mem_antidiagonal.mp hp; omega)]
lemma banner_begin (F : Topaz I (HeatS X))(T: Finset I): banner T F borne (upstart X) 0=banner T (fun i=> F i 0) gust (spine_one X) := by
   induction T using strongInductionOn with
   | _ t ih=>
    rw [banner,banner]; by_cases h:t=∅; · rw [if_pos h,if_pos h]; exact if_pos rfl
    rw [if_neg h,if_neg h,Pi.smul_apply,Finset.sum_apply]; congr 1; refine sum_congr rfl fun p _=>?_ ; rw [borne_z,ih p.val.2 ?_]; · rfl
    exact Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_product.mp (mem_filter.mp (mem_filter.mp p.property).1).1).2,fun v=>not_lt_of_ge (congr_arg Finset.card v).ge (shrank _ p.property)⟩
lemma banner_z (p : Option Side) (hk:Whole K)(he:Gets S)(hu:∀ t,Sails (vanes a t) (U t)) (t:Finset I): Sails (vanes a t) (banner t U gust (spine_one X)):= by
  have hp := (walksR (pulse_ok U hk he hu (p:=p)) t) 0
  rw [banner_begin,show (fun i=> pulse p K S U i 0)=U from funext (pulse_z U)] at hp; exact hp
-- Finite glee; cover relic next
lemma page_rose (hp:Whole K)(hd:Gets S)(he: (K.acts L)ᵀ=K.acts L)(hs:∀ i,Sails (vanes a i) (U i))(hx:U ∅=0)(o:Site L)(k:Finset I) :
    glee (vanes a k) o (banner k (pulse (some L) K S U) borne (upstart X))=glee (vanes a k) o (murmur (some L) K S (banner k U gust (spine_one X))) := by
  let p:=some L; let F:= pulse p K S U; have hF := (pulse_ok U hp hd hs (p:=p)); have hL := pulse_void U hp hd hx (p:=p); let V i:=banner i F borne (upstart X); have hG:= walksR hF
  let f i:=glee (vanes a i) o (F i); let g i:=glee (vanes a i) o (V i); let P:=K.acts L
  let S' := Beats K S L
  have hx : rust f= action (coda P S') f+(1/2:ℝ) • archs P f f:= by
    rw [← show _=action (coda P S') f+(1/2:ℝ) • archs P f f from lever_attain hF hp hd o]; funext t
    rw [← show ticks (F _)= _ from tip_paid (p:=p) (K:=K) (S:=S) U t,tallyD (p:=o) (hF t)]; rfl
  have h := timed_mark P S' he (bloom_g hF hL o) (fun i=>glee_sway (hF i) o) (fun i=> glee_sway (hG i) o) hx
  let G:=banner k U gust (spine_one X); let T:=glee (vanes a k) o (murmur p K S G); change g k=T
  refine time_once P S' _ _ (congr_fun h k) ?_ ?_
  · have ht : Sails (vanes a k) G:= banner_z p hp hd hs k; exact (pendants o hp (fun i j=>(hd.2 i j).1) hd.1 ht.tide ht.budget).2.2
  funext i; unfold g V T glee; rw [banner_begin,show (fun i=> F i 0)=U from funext (pulse_z U)]; rw [show murmur p K S G 0=G from funext fun i=>funext fun k=> by rw [murmur]]
end YM.RG08.Wax

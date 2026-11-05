import YM.RG08.Necks.Cards
/-! # Individual pitch & pair tests at post receipts, repeating pre specified.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Clef
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries
variable {G:Gauge}{n m d p l e k c:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "A"=>Loc G 1
local notation "E"=> Ed G Cover
variable (X:Labels.Frame G d)
lemma Ready.two {Z Z':Pack n E}(a:ℝ)(he:Ready k G n Z)(h:Ready k G n Z'):Ready k G n (Z+a • Z'):=by
 have hv:=Atrium.Ready_sum (M:=fun i:Bool=>bif i then Z else Z') univ (fun i=> bif i then (1:ℝ) else a) (fun i _=>by cases i; exact h;exact he)
 simpa only [Fintype.sum_bool,cond_true,cond_false,one_smul] using hv
lemma pix_two {Z Z':Pack n E}(a:ℝ)(he:Ready k G n Z)(h:Ready k G n Z')(i:X.Index)(v:pedal):pix X i v (Z+a • Z')=pix X i v Z+a*pix X i v Z':=by
 have hv:=pix_clock X i v (M:=fun i:Bool=>bif i then Z else Z') univ (fun i=> bif i then (1:ℝ) else a) (fun i _=>by cases i; exact h;exact he)
 simp only [Fintype.sum_bool,cond_true,cond_false,one_smul,one_mul] at hv; exact hv
lemma Ready.minus {Z Z':Pack n E}(he:Ready k G n Z)(h:Ready k G n Z'):Ready k G n (Z-Z'):=by rw [show Z-Z'=Z+(-1:ℝ) • Z' from by module];exact Ready.two _ he h
lemma pix_minus {Z Z':Pack n E}(he:Ready k G n Z)(h:Ready k G n Z')(i:X.Index)(v:pedal):pix X i v (Z-Z')=pix X i v Z-pix X i v Z':=by rw [show Z-Z'=Z+(-1:ℝ) • Z' from by module,pix_two X _ he h];ring
lemma pix_plus {Z Z':Pack n E}(he:Ready k G n Z)(h:Ready k G n Z')(i:X.Index)(v:pedal):pix X i v (Z+Z')=pix X i v Z+pix X i v Z':=by rw [show Z+Z'=Z+(1:ℝ) • Z' from by simp,pix_two X _ he h,one_mul]
lemma ballot_minus {S S':GrainS E}(he:Folk p l S)(hf:Folk p l S')(i:Accent X):project X (S-S') e i=project X S e i-project X S' e i:=by
 unfold project;rw [← Finset.sum_sub_distrib];apply sum_congr rfl;intro k _;split_ifs
 · exact pix_minus X (permit_ready he.inlet) (permit_ready hf.inlet) i.ear i.test.play
 rw [sub_zero]
-- universal W before L depends Frame & fixed demands. Price for any n ≤ d f∈Cue ranks etc. paired mode.
lemma pitch (D:ℕ)(η:ℝ)(ht:0<η):∃ C:ℝ,0≤C ∧ ∀ (o:Accent X)(n:ℕ),n≤d→∀ S:Pack n E,Lyrics S→ ∀ B:ℝ,0≤B→Sings (stance _) D ht S B→|pix X o.ear o.test.play S|≤C*B:=by
 obtain ⟨C,hC,H⟩:=pix_prize X D η ht
 exact ⟨C,hC,fun o n h S hs B hb h'=> H n h S B hb hs h' o.ear o.test⟩

-- Extra estimate variant: variation on same component post part **depends only on ABSOLUTE** spender of F', not throughput charge T in portFee lift.
lemma comet (n d:ℕ):∃ H:ℝ→ℝ,Wage H∧ ∀{G:Gauge}{P:Patch}{K:KernelChoices}{Q R:Crew G P K}{σ η δ W:ℝ}{e D:ℕ}(_h:Warmth η δ W e n d Q R)(hp:0<σ)(he:0<η)(_hη:η≤1)(_hσ:η*Carrier.unitStep P.L≤σ)(S:GrainS (Ed G Cover)){B:ℝ}(_hB:0≤B)(_hs:Lyrics (S e n))(_hS:Sings (stance _) D hp (S e n) B),
 let x:=Q.cast d S e n;let u':=R.cast d S e n
 ; Dyad (stance _) D he (H W*B) δ x u':=by
 let H(x:ℝ):= x*((n+1:ℝ)*Real.exp 16*x^n)
 refine ⟨H,Wage.input.mul ((Wage.constant _ (by positivity)).mul (Steam.wagepow n)),?_⟩
 intro G P K Q R σ η δ W e D h hp he hη hσ S B hB hs hS x u'
 have hx:=cloud_opt P d h.tooth.gift (fun i=>ridges_price (e:=e) (n:=n) (G:=G) (S:=S) (S':=S) h.tooth i he hη hσ (Dyad.pure h.tooth.gift hB hs hS));rw [←cloud_expr,←cloud_expr] at hx
 apply hx.mono;unfold H;apply le_trans (mul_le_mul_of_nonneg_right h.glow (show 0≤((n+1:ℝ)*(Real.exp 16*B)*W^n) from by have hv:0 ≤ W:=zero_le_one.trans h.tooth.base;positivity));exact le_of_eq (by ring)
end YM.RG08.Necks

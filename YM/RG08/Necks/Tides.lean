import YM.RG08.Necks.Circus
/-! # Deterministic leg tick meets:
 Same-component & cut variation before reset. χ small at e>0. Q shape PSD.
 Costs pre and post carefully segregated.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Clef
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries
variable {G:Gauge}{n m d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "A₀"=>Loc G 1
local notation "E"=> Ed G Cover
-- prework chosen common
structure Novice (σ τ η μ V:ℝ)(d D l e n j t:ℕ):Prop where
 paid :0<σ
 pre :0<τ
 out':0<η
 Khip:0≤V
 rank:n≤l+e
 smoothing:4≤j
 charge:4≤t
 horizon:d≤j
 tax:d+1≤D
 sup:0≤μ
 max:μ≤1
 high : (↑((e+1)*(l+e)):ℝ)*μ≤σ/2
 next : 2*η≤τ
 warm:η≤1
structure Stream (σ τ η μ V W:ℝ)(d j t:ℕ){K:KernelChoices}(Q:Crew G P K):Prop where
 congruent:Odd P.L.val
 firing: (2*η)/(P.L.val:ℝ)≤μ
 nim : η*Carrier.unitStep P.L≤σ/2
 safe:1≤W
 scale:(P.L.val:ℝ)^d≤W
 place:RowCost τ P.L (Cell.plotted P K G Q.fine) W
 route:
  ∃(F:Flight j t)(x:P.L=F.L)(b:Kernel G.ColorIndex (Loc G 1)),let m:Carrier.Lines P.L:= (x.symm ▸ Carrier.linesOf F K.penalty)
  ; RowCost τ P.L b W∧Tutor P.L τ V m G d∧ Crest P.L m b (Cell.plotted P K G Q.fine)


variable (X:Labels.Frame G d)
-- match Q sponsorship for Dir T0. support pure leading with grade w and amount χ measured in full normalized project. note Deriv read factor κ/ path. exports constants pre(L) with two scalings
lemma drive (H:Hol G)(l D e n j t:ℕ)(σ τ η μ V:ℝ)(h:Novice σ τ η μ V d D l e n j t)(K:KernelChoices):∃ A:ℝ,∃ J:ℝ→ℝ,1≤A ∧ Week (driveR n) J ∧ (∀ W:ℝ,1≤W→1≤J W) ∧ ∀ {P:Patch}{Q:Crew G P K}{W:ℝ},Stream σ τ η μ V W d j t Q→∀{S:GrainS (Ed G Cover)},Folk D l S→∀ (w:ℕ)(B T T' χ:ℝ), (∀ i<e,∀ k≤l+i,Sings (stance _) D h.paid (S i k) B) → (∀ k≤l+e,Sings (stance _) D h.paid (S e k) T)→ Sings (stance _) D h.paid (S e n) T'→0≤χ →0≤B→0≤T→0≤T'→(∀ c:Accent X,octave c=n→|project X S e c|≤χ)→
 w≤d→(w=0 ∨ B=0 ∧ ∀ c:Accent X,octave c=n→ gamut c<w→project X S e c=0)→
 let u:=P.L;let a:ℝ:=u.val;let U:=Q.cast d S e n; let E₁:=A*T'*Carrier.unitStep u+J W*(B+χ)
 ; Sings (stance _) D h.out' U E₁ ∧ Ready D G n U∧∀ c:Accent X,octave c=n→ |pix X c.ear c.test.play U|≤ A*χ*a^(d-w)+J W*B ∧(gamut c≤w→B=0→pix X c.ear c.test.play U=a^(d-gamut c)*pix X c.ear c.test.play (S e n)) :=by
 -- last comparator `pix ... of P` maps to project only if e=0 OR B=0; if B=0 for e>0 then lower S all zero in Sings→ zero, yes. prove later, simplify RHS to pix P S.
 obtain ⟨C,hC,Y⟩:= Trill.podium X H D 0 l e n j t σ τ η μ V h.paid h.pre h.out' h.Khip h.rank h.smoothing h.charge h.tax h.horizon h.sup h.max h.high h.next K
 let a:=1+C
 let J(W:ℝ):= (1+C)*((W+V)^n+1)*W
 have hv:= h.Khip
 have hall:= Week.pow (Week.variable0.add (Week.fixed _ hv)) n
 have haW: Week 0 (fun (_:ℝ)=>1+C):=Week.fixed _ (by positivity)
 have hcW:Week 0 (fun (_:ℝ)=>(1:ℝ)):=Week.fixed _ (by positivity)
 have hJ: Week (driveR n) J:=by
   have hy:Week (0+(max ((max 1 0)*n) 0)+1) J :=(haW.mul (hall.add hcW)).mul Week.variable0 -- typo grade first factor 0+ not max
   simpa [driveR] using hy
 have hw(W:ℝ)(hW:1≤W): 1≤J W:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith only [hC]) (le_add_of_nonneg_left (by positivity))) hW
 refine ⟨a,J,(by unfold a;linarith only [hC]),hJ,hw,?_⟩
 intro P Q W J' S hs w B T T' χ hB hT hT' hχ hb ht ht' hK hD hW u a' U E' -- remove KMu
 obtain ⟨F,x,b,hE,hU,hStar⟩:=J'.route
 have hz:1 ≤ W:= J'.safe;have hd:(0:ℝ)≤a':= Nat.cast_nonneg _
 obtain ⟨hy,hf⟩:=Y P F Q.fine S b x w J'.congruent hE J'.place (zero_lt_one.trans_le hz) hU hStar J'.firing J'.nim hs.outlet hs.inlet ht ht' hb hχ hT hT' hB hK hD hW
 let E₀:= (W+V)^n
 have hF: (a':ℝ)^d≤W:=J'.scale
 have hg:1≤E₀:=one_le_pow₀ (by linarith only [hz,hv])
 have hq:0 ≤ C*T'*Carrier.unitStep P.L:=mul_nonneg (mul_nonneg hC ht') (Carrier.unitStep_pos _).le
 have h₃ : C*(E₀+1)*W≤J W:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only : C ≤ 1+C) (by linarith only [hg])) (by linarith)
 have ha: Sings (stance _) D h.out' U E':=by
    refine hy.mono le_rfl le_rfl (fun _=>le_rfl) ?_
    have hc:C≤a:=by unfold a; linarith only
    -- C * ((W+V)^n * B * L^d+(χ+B)*L^d) ≤ J*(B+χ)
    have h1:=mul_le_mul h₃ (le_refl (B+χ)) (by linarith only [hb,hχ]) (by unfold J;positivity)
    have ht0:E₀*B+ (χ+B)≤(E₀+1)*(B+χ):=by nlinarith only [hχ,hg]
    have h2:=mul_le_mul ht0 hF (by positivity :0 ≤ a'^d) (by linarith only [hb,hχ,hg,show 0≤(E₀+1)*(B+χ) from by positivity])
    change C*T'*Carrier.unitStep P.L+C*(E₀*B*a'^d+(χ+B)*a'^d)≤a*T'*Carrier.unitStep P.L+J W*(B+χ)
    nlinarith only [h1,h2,hC,hc,mul_nonneg ht' (Carrier.unitStep_pos P.L).le,show C*( (E₀+1)*(B+χ)*W-(E₀*B+(χ+B))*a'^d)≥0 from mul_nonneg hC (sub_nonneg.mpr h2)]
 obtain ⟨HL,H'⟩:=Trill.foreLyrics K Q.fine S (Trill.permit_ready hs.inlet (n:=n) (e:=e)) J'.place h.pre (zero_lt_one.trans_le hz) d
 refine ⟨ha,⟨HL,H',η,h.out',E',(by unfold E' a;have hu:0≤Carrier.unitStep u:= (Carrier.unitStep_pos _).le;have he :0≤J W:=zero_le_one.trans (hw _ hz);positivity) ,ha⟩,?_⟩
 intro i hi;refine ⟨(hf i hi).1.trans ?_,(hf i hi).2⟩
 change C*(E₀*B*a'^d+(χ+B)*a'^(d-w))≤ a*χ*a'^(d-w)+J W*B
 have hh:(a':ℝ)≥1:=Nat.one_le_cast.mpr P.L.property
 have h2:a'^(d-w)≤W:=(pow_le_pow_right₀ hh (Nat.sub_le ..)).trans hF
 have ht0:E₀*a'^d+a'^(d-w)≤(E₀+1)*W:=by nlinarith only [h2,hF,hg]
 unfold a
 nlinarith only [show 0 ≤ χ*a'^(d-w) from by positivity,mul_le_mul_of_nonneg_left ht0 (mul_nonneg hC hb),mul_le_mul_of_nonneg_right h₃ hb]
end YM.RG08.Necks

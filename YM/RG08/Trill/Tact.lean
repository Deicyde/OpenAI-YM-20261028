import YM.RG08.Trill.Snaps
import YM.RG08.Halo.Tuners
import YM.RG08.Trill.Hex
/-!
Called marker.

Lower fees at requested D only, frame rank across all, pre budgets.

Polls unnormalized derivative Pal (no ν ration).
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k:ℕ}{σ B Q:ℝ}
local notation "E₀"=>Ed G Cover
local notation "Y"=>Snap G d
local notation "N"=>Nd G Cover
local notation "A₀"=>Loc G 1
variable (X:Labels.Frame G d)
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 900000
lemma mintCount (D n l e:ℕ)(σ:ℝ)(hs:0<σ)(Ho:Hol G):∃ C:ℝ,0≤C ∧ ∀{P:GrainS (Ed G Cover)}(B T Q:ℝ),Calls l P→Permit D l P→0≤B→0≤T→0≤Q→(∀ i<e,∀ k≤l+i,Sings (stance _) D hs (P i k) B)→(∀ k≤l+e,Sings (stance _) D hs (P e k) T)→∀ (b:Fin n→ℕ)(q:ℕ)(r:Jetty.Cargo q)(f:Fin n→Masked G)(a:Fin n→ℝ),q+(∑ i,b i)≤d →(∀ i,1≤b i)→(∀ i,Chit G (b i) (f i) (a i))→(∀ c:Accent X, (X.grades c.ear).1+weight c.test.play≤q+(∑ j,b j)→(X.grades c.ear).2=n→weight c.test.play=q→ |project X P e c|≤Q)→
 |sonic (P e n) (pal r) (Yurt.inlet ∘ f)|≤ (∏ i,a i)*(C*(B+Q)):=by
 by_cases hV:n≤l+e;swap
 · refine ⟨0,le_rfl,fun {_} B T Q Hc Hp _ _ _ _ _ _ q r f _ _ _ _ _=>?_⟩
   have hh:=not_not.mp (fun h=> hV (Hp.lit e n h)); -- need expected
   rw [hh];unfold sonic; simp [tote]
 obtain ⟨U,hU,Hw⟩:= spark_band G l e n (d+1) σ 0 hs (le_rfl) zero_le_one (by rw [mul_zero];exact (half_pos hs).le) hV
 obtain ⟨V,hV',H⟩:= hymn X D n σ hs Ho
 choose c hc Hq using fun i:Fin (d+1)=>counterpart G d i.val (Nat.le_of_lt_succ i.isLt)
 let W:=∑ i:Fin (d+1),c i; have hw:0 ≤ W:=sum_nonneg fun i _=>hc _
 let R:=∑ i:Fin (d+1),∑ j:Jetty.Cargo i.val,Jetty.beam D hs (pal j)
 have hr:0 ≤ R:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>beam_nn ..
 let C:=(U*W^n*R+V*W^n);have hC:0≤C:=by unfold C;positivity
 refine ⟨C,hC,fun {P} B T Q Hc Hp hB hT hQ hx hy b q r f a hb h₁ H₁ H₂=>?_⟩
 let j(i:Fin n):Fin (d+1):=⟨b i,Nat.lt_succ_of_le (le_trans (single_le_sum (f:=b) (fun _ _=>Nat.zero_le _) (mem_univ i)) ((Nat.le_add_left _ _).trans hb))⟩
 choose z x Hz Hs HA Ho' he using (fun i=> Hq (j i) (V:=f i) (B:=a i) (H₁ i))
 let M:=P e n;let p:=d+1
 have hh(i):0≤a i:=(H₁ i).live
 let K(i:Fin n):=W*a i
 have hD(i):c (j i)≤W:=single_le_sum (s:=univ) (f:=c) (fun _ _=>hc _) (mem_univ (j i))
 have hL(i):c (j i)*a i≤K i:=mul_le_mul_of_nonneg_right (hD i) (hh i)
 have hx'(i):Bearing (stance _) p 0 (K i) (x i):=((HA i).here le_rfl (Nat.add_le_add_right (show b i ≤ d from Nat.le_of_lt_succ (j i).isLt) _)).up (hL i)
 have hz(i):Bearing (stance _) p 0 (K i) (pluck 1 (z i)):=((Ho' i).here le_rfl (by omega: d≤p)).up (hL i)
 have hu:Jetty.beam D hs (pal r)≤R:=by
    let t:Fin (d+1):=⟨q,by omega⟩
    apply (single_le_sum (s:=univ) (f:=fun v:Jetty.Cargo q=> Jetty.beam D hs (pal v)) (fun v _=>beam_nn ..) (mem_univ r)).trans (single_le_sum (s:=univ) (f:=fun v:Fin (d+1)=>∑ i:Jetty.Cargo v.val,Jetty.beam D hs (pal i)) (fun _ _=>sum_nonneg fun _ _=>beam_nn ..) (mem_univ t))
 let S:=pluck 1 ∘ z; let G':=Yurt.inlet ∘ f
 let Y1:=sonic M (pal r) S; let Y2:=sonic M (pal r) G'
 have hF:= (Hw S x K hz hx' P D B T (pal r) Hc Hp hB hT hx hy).1
 have HE: G'=fun i=>S i+grad (x i):=funext fun i=>he i
 have hM: ∏ i,K i=W^n * ∏ i,a i:=by unfold K;rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
 have hp:0 ≤ ∏ i:Fin n,a i:=prod_nonneg (fun _ _=>hh _)
 have hU':|Y2-Y1|≤U*(W^n * ∏ i,a i)*B*R:=by
    unfold Y1 Y2;rw [HE,←hM];apply hF.trans; apply mul_le_mul_of_nonneg_left hu;rw [hM];positivity
 have hn:n≤d:= by
    have hl:n≤∑ i,b i:= by simpa using sum_le_sum (s:=univ) (f:=fun (_:Fin n)=>1) (g:=b) fun i _=>h₁ i
    omega
 have Ht:|Y1|≤V*(B+Q)*(W^n *∏ i,a i):= (H e Hc Hp q r b z hb hn Hz B Q hB hQ hx H₂).trans (mul_le_mul_of_nonneg_left (by rw [←hM];exact prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>(Hs _).trans (hL _))) (by positivity))
 change |Y2|≤_
 have hE:|Y2|≤|Y2-Y1|+|Y1|:=by nth_rw 1 [show Y2=Y2-Y1+Y1 from by ring];exact abs_add_le ..
 apply (hE.trans (add_le_add hU' Ht)).trans
 unfold C; nlinarith only [show 0≤U*W^n*R*(∏ i,a i)*Q by positivity]
def Verdict (_X:Labels.Frame G d)(W n D:ℕ)(F:Pack n (Ed G Cover))(σ B:ℝ)(hs:0<σ) :Prop:=Halo.Tuned G n d D W σ hs F B
lemma chime (D n l e:ℕ)(σ:ℝ)(hs:0<σ)(Ho:Hol G):∃ C:ℝ,0≤C∧ ∀ {P:GrainS (Ed G Cover)}(B T Q:ℝ),Calls l P→Permit D l P→0≤B→0≤T→0≤Q→(∀ i<e,∀ k≤l+i,Sings (stance _) D hs (P i k) B)→(∀ k≤l+e,Sings (stance _) D hs (P e k) T)→(∀ c:Accent X,(X.grades c.ear).2=n→|project X P e c|≤Q)→
 ∀ w≤d+1, (w=0 ∨ (B=0 ∧ ∀ c:Accent X,(X.grades c.ear).2=n→(X.grades c.ear).1+weight c.test.play<w→project X P e c=0))→Verdict X w n D (P e n) σ (C*(B+Q)) hs:=by
 obtain ⟨C,hC,H⟩:= mintCount X D n l e σ hs Ho
 refine ⟨C,hC,fun {P} B T Q Hc Hp hB hT hQ hV hw hk w hh hy=>?_⟩
 have ht:Sings (stance _) D hs (P e n) T:=by
    by_cases he:n≤l+e;exact hw _ he
    rw [not_not.mp fun h=>he (Hp.lit e n h)];exact tin
 refine ⟨(Hp.price e n).1,⟨T,hT,ht⟩,fun b t r V v h hb hD=> H B T Q Hc Hp hB hT hQ hV hw b t r V v h hb hD (fun c _ he _=>hk c he),fun b t r V h hD=>?_,by positivity⟩
 obtain rfl|⟨rfl,h₃⟩:=hy;omega
 by_cases hb:∀ i,1≤b i
 · choose a ha using fun i=>chitQual (hD i)
   have hx:= H 0 T 0 Hc Hp hB hT le_rfl hV hw b t r V a (by omega) hb ha (fun g hg he _=>by rw [h₃ g he (hg.trans_lt h),abs_zero])
   exact abs_eq_zero.mp (le_antisymm (by simpa using hx) (abs_nonneg _))
 push Not at hb;obtain ⟨i,hi⟩:=hb
 have hz:V i∈Place.rangeLt _ 0:= (show b i=0 by omega) ▸ (hD i)
 obtain ⟨q,_,hr⟩:=Halo.reading _ hz
 apply sonic_zero (X:=Yurt.inlet ∘ V) (i:=i) _ (pal r)
 funext j;unfold Function.comp Yurt.inlet;rw [←hr,Halo.mix,sum_of_isEmpty];rfl
end YM.RG08.Trill

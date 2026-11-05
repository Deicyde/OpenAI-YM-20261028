import YM.RG08.Sideshow.Glaze
import YM.RG08.Sideshow.Elevation
/-! # Structural local repeat estimate. Uniform inertia and rough T_ro. Uses all data
 from `Podium` on each admitted, nontruncated forecast. No iterative physical hypotheses.
- paired split of repeated propagations F & Same; then support does compression.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sideshow
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Room Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Necks
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries Matrix
variable {G:Gauge}{n D d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
variable (X:Labels.Frame G d)
local notation "E"=>Ed G Cover
local notation "I₀"=> Accent X
local notation "M₀"=>Playbook X
local notation "S₀"=>Bouquet X
local notation "A₀"=>Loc G 1
local notation "Δ"=>stance A₀
local notation "Ic"=> (Fintype.card (Accent X):ℝ)

structure Penny (T:Playbook X)(r l e:ℕ)(B:ℝ):Prop where
 collects i j:octave i=l→ r ≤octave j→ |dusk e T j i|≤ B
structure Stamps (D e n l:ℕ)(B δ:ℝ){σ η:ℝ}(hs:0<σ)(ht:0<η)(S S' Y Y':Bouquet X)(M N:M₀):Prop where
 base :1≤B
 before i a r: octave i=l→ ( r≤l+a→(a<e∨a=e∧n<r)→ Dyad Δ D hs B δ (S i a r) (S' i a r))
 after0 i a r:a<e∨a=e∧ octave i<l→ Dyad Δ D ht B δ (Y i a r) (Y' i a r)
 currency a i j:a<e→ |tap a (M j i)|≤B ∧ |tap a (N j i)|≤B ∧ |tap a (M j i)-tap a (N j i)|≤B*δ
structure Replies (D e n l:ℕ)(A B C' B0 B1 g δ T:ℝ){η:ℝ}(h:0<η)(S S':Bouquet X)(M N:M₀):Prop where -- A pre, B post uniform polynomial, C'var post, B0 throughput & birth,currence T var
 mint: ∀ i∈booth X l,Sings Δ D h (S i e n) (A*B0/g+B) ∧ Sings Δ D h (S' i e n) (A*B1/g+B)
 venue: ∀ i∈booth X l,Sings Δ D h (S i e n-S' i e n) (A*T/g+C'*δ)
 tide: Penny X M n l e B∧Penny X N n l e B
 calm: Penny X (M-N) n l e (C'*δ)

private lemma bills (A B c y m u D B1 f g:ℝ) (hA:1 ≤ A)(hB:1 ≤ B)(hc:1 ≤ c)(hy:0 ≤ y)(hM:1 ≤ m)(hu:0 ≤ u)(hD:0 ≤ D)(h1:0 ≤ B1)(hg:1 ≤ g)(hf:1 ≤ f)
 (hF:8*(A+u+y+D+m+c) ≤ f):
 let γ (V:ℝ):= u*A*V/g+u*(m*(B+1)+y*(c*B)*(c*B)); let x:=B+B1; let G:=c*x
 ; (∀ V:ℝ,γ V≤u*A*V/g+(f^10)*B^2) ∧ u*(m*x+y*G^2+D*G*γ B1)≤f^10*x^4 ∧ c≤f^10∧1≤f^10:=by
 intro γ x G
 have hA': A≤f:=by linarith
 have hu': u≤f:=by linarith
 have hm: m ≤f/8:=by linarith
 have hy': y ≤f/8:=by linarith
 have hb:0 ≤ c:=zero_le_one.trans hc
 have hn:0 ≤ B:=by linarith
 have hc': c ≤ f:=by linarith
 have hD': D ≤ f/8:=by linarith
 have hf':0 ≤ f:=zero_le_one.trans hf
 have hM':0 ≤ m:=by linarith
 have hx':1≤x:=by unfold x; linarith
 have hγ(V:ℝ): γ V ≤ u*A*V/g+f^4*B^2:=by
    have h: u*(2*m+y*c^2)≤ f^4:=by
      calc
       _ ≤ f*(2*(f/8)+(f/8)*f^2):=by gcongr -- use remaining
       _ ≤_:=by nlinarith only [show f^2≤ f^4 from pow_le_pow_right₀ hf (by norm_num)]
    unfold γ
    nlinarith only [mul_le_mul_of_nonneg_left (show B+1≤ 2*B^2 by nlinarith only [hB]) (mul_nonneg hu hM'),mul_le_mul_of_nonneg_right h (sq_nonneg B)]
 have ht:g ≥ 0:=by linarith
 have hg': γ B1 ≤ (f^2+f^4)*x^2:= by
    have h2:u*A*B1/g ≤ f*f*x:= (div_le_self (by positivity) hg).trans (by unfold x; gcongr; exact le_add_of_nonneg_left hn)
    have h3:B≤x:=by unfold x; linarith
    have h4:f^4*B^2 ≤ f^4*x^2:=by gcongr
    nlinarith only [h2,h4,hγ B1,mul_le_mul_of_nonneg_left (le_self_pow₀ hx' (show (2:ℕ)≠0 from by omega)) (sq_nonneg f)]
 have hq:f ≤ f^10:=le_self_pow₀ hf (by norm_num)
 refine ⟨fun V=> (hγ V).trans (by gcongr; norm_num), ?_,hc'.trans hq,one_le_pow₀ hf⟩
 unfold G
 have hx0:0≤x:=by linarith
 calc
  _ ≤ f*((f/8)*x+(f/8)*(f*x)^2+(f/8)*(f*x)*((f^2+f^4)*x^2)):=by
    have hz:0≤γ B1:=by unfold γ;positivity
    gcongr -- indent & assumptions
  _ ≤ _:=by
    have ht(i j:ℕ)(hi:i≤10)(hj:j≤4): f^i*x^j≤ f^10*x^4:=mul_le_mul (pow_le_pow_right₀ hf hi) (pow_le_pow_right₀ hx' hj) (by positivity) (by positivity)
    nlinarith only [ht 2 1 (by norm_num) (by norm_num),ht 4 2 (by norm_num) (by norm_num),ht 5 3 (by norm_num) (by norm_num),ht 7 3 (by norm_num) (by norm_num),show 0≤f^10*x^4 from by positivity]

set_option maxHeartbeats 650000
/-- one-step precise lower DAG. Post budgets Wage(W), W pay stage lamps. Demand g^d pinned in Warmth. C' factor uses (B+β_N) squared for known accounts. includes Ξ_T palettes.
 Outputs require normalized Bright matching and triangular radial chart, implicit.
-/
theorem harbor (D k j t l e n:ℕ)(H:Hol G)(K:KernelChoices)(σ η τ μ V:ℝ)(hf:Font d D k j t σ τ η μ V)(hl:l≤d)(he:e≤k)(hn:n≤l+e):∃ A:ℝ,∃ J:ℝ→ℝ,1≤A∧Week (transitR n e l d k) J ∧ (∀ W≥1,1≤J W) ∧ ∀ {P:Patch}{Q R:Crew G P K}{W δ:ℝ},Race σ τ η μ V W δ D d k (d+k) j t Q R→0<δ→∀ {S S':Bouquet X},Silo X D k hf.fine S → Silo X D k hf.fine S' →
 let Y:=sing X Q S; let Y':=sing X R S';let M:=deposit X Q S;let N:=deposit X R S';let g:ℝ:=P.L.val
 ; ∀ {B B0 B1 T:ℝ},Stamps X D e n l B δ hf.fine hf.coarse S S' Y Y' M N → 0≤B0→0≤B1→0≤T→(∀ i∈booth X l,Sings Δ D hf.fine (S i e n) B0∧ Sings Δ D hf.fine (S' i e n) B1 ∧ Sings Δ D hf.fine (S i e n-S' i e n) T) →
 Replies X D e n l A (J W*B^2) (J W*(B+B1)^4) B0 B1 g δ T hf.coarse Y Y' M N:=by
 obtain ⟨C,hC,Y⟩:=oneWing X D k j t K σ τ η μ V H hf
 obtain ⟨A,J,hA,hJ,H⟩:=DocketBill X D l e n j t (d+k) H K σ η τ μ V (hf.hired l e n hl he hn) (by omega) (by omega)
 let u:=Ic*plum (Accent X) d C;have hIc:0 ≤ Ic:=Nat.cast_nonneg _
 have hU:0 ≤ u:=mul_nonneg hIc (plum_nn (by linarith))
 let v(W:ℝ):=A*W+J W; let y:ℝ:=Ic*((e:ℝ)+2)*2;have hy:0≤y:=by unfold y; positivity
 -- t = vW*B≥B covers abs M at focal range, vW*(B+B1) covers variation (*δ). answering costs pre*u, post up to u* (2*J +y*v^2) * B^2. variation P.W^4 inc q. absorb.
 let w(W:ℝ):=(1+A+u+y+Ic+J W+v W)*8
 let q(W:ℝ):=(w W)^10
 have hv:=fun W hW=> (H W hW).1
 have hv0:Week (max (0+1) (docketR n e l d (d+k))) v:= ((Week.fixed _ (by linarith)).mul Week.variable0).add hJ
 let r:=docketR n e l d (d+k)
 have hw:Week ((max (max 0 r) (max (0+1) r))+0) w:=((((((Week.fixed _ (by positivity [hA]))).add hJ).add hv0)).mul (Week.fixed 8 (by norm_num)))
 have hW {W:ℝ}(h:1≤W):1≤w W:=by have :=hv W h;unfold w v;nlinarith only [this,hA,h,hU,hy,hIc]
 let C':=1+u*A;have hc':1≤C':=le_add_of_nonneg_right (mul_nonneg hU (by linarith))
 refine ⟨C',q,hc',?_,fun _ h=>one_le_pow₀ (hW h),?_⟩
 · simpa [transitR,r] using hw.pow 10
 intro P Q R W δ hx hδ S S' hS hS' N N' E' E'' g B B0 B1 T hB hB0 hB1 hT hF
 obtain ⟨hR,hR'⟩:=Y hx hδ hS hS'; let m:=J W
 let c:=v W;let f:=w W; have hW0:=hx.aps.tooth.base; have hm:= hv W hW0
 have hc1:1≤c:=by unfold c v;nlinarith only [hW0,hm,hA]
 have hf':=show 1≤f from hW hW0
 have hb': B≥1:=hB.base;have hb:0 ≤ B:=by linarith
 have hg:0<g:=Nat.cast_pos.mpr P.L.pos
 have ticket(i:I₀)(hi:octave i=l):Docket X Q R D e l n A m η 1 B B1 B0 T δ hf.coarse 0 (S i) (S' i):=by
    obtain ⟨b,h⟩:=deckAll X hS.seats hS'.seats hS.unbound hS'.unbound hδ i e he;rw [hi] at h;have he':=h n hn
    obtain ⟨h0,h1,hX⟩:= hF _ ((booth_in X).mpr hi)
    exact (H W hW0).2 ⟨hx.aps.prices he le_rfl,hx.sold,hx.sold'⟩ (hi ▸ hS.unbound i) (hi ▸ hS'.unbound i) B b B0 B1 T 1 hb he'.price hB0 hB1 hT zero_le_one (fun a j=>hB.before i a j hi) (fun i hi=>⟨(h i hi).near,(h i hi).far⟩) he' h0 h1 hX (fun j _=> (clean_criterion X S hS.merit S' hS'.merit i e).1 j) _ (by omega) (.inl rfl)
 have ha:0≤A:=zero_le_one.trans hA
 have hF'(S:S₀)(q:Crew G P K)(i:I₀)(h:octave i=l): q.land d l (S i)=play q S i:=by rw [←h];rfl
 have hhF(i j:I₀)(h:octave i=l)(ht:n≤octave j):=
       (ticket i h).booth j ht
 have hV(i j:I₀)(h:octave i=l)(ht:n≤octave j): |tap e (E' j i)| ≤ c*B ∧ |tap e (E'' j i)|≤ c*B ∧ |tap e (E' j i)-tap e (E'' j i)|≤c*(B+B1)*δ:=by
    change |tap e (ballot _ _)|≤_ ∧ |tap e (ballot _ _)|≤_ ∧ |tap e (ballot _ _)-tap e (ballot _ _)|≤_
    rw [ballot_value,ballot_value]; unfold play;rw [h]
    have hh:=hhF i j h ht; dsimp only at hh
    have hq:A*1*g^(d-0)+m*B≤ c*B:=by
       have h':g^d≤W:=hx.aps.glow
       unfold c v;rw [Nat.sub_zero];unfold m;nlinarith only [ha,h',hW0,hb',hA, mul_nonneg ha (sub_nonneg.mpr h'), mul_nonneg (mul_nonneg ha (by linarith only [hW0] : 0 ≤ W)) (sub_nonneg.mpr hb')]
    have hX: m*(B+B1)*δ≤ c*(B+B1)*δ:=by
        have he:m≤c:=by unfold c m v;nlinarith only [hW0,hA]
        gcongr
    exact ⟨hh.1.trans hq,hh.2.1.trans hq, hh.2.2.1.trans hX⟩
 have hCl:= (overjoy X Q S hS.unbound).2;have hCr:Cloth E'':=(overjoy X R S' hS'.unbound).2
 have hN:Threads D N:=hR.rises.unbound;have hN':Threads D N':=hR'.rises.unbound
 have hvB:B≤ c*B:=le_mul_of_one_le_left hb hc1
 have hJe(i): octave i=l → Sings Δ D hf.coarse (play Q S i e n) (A*B0/g+m*(B+1))∧ Sings Δ D hf.coarse (play R S' i e n) (A*B1/g+m*(B+1))∧Sings Δ D hf.coarse (play Q S i e n-play R S' i e n) (A*T/g+(m*(B+B1))*δ):=by
    intro hi;rw [← hF' S Q _ hi,←hF' S' R _ hi]; exact ⟨((ticket _ hi).fare.1.cost0),((ticket _ hi).fare.2.cost0),(ticket _ hi).rated.spent⟩
 have h0':Candor (D:=D) hf.coarse X e l n N N E' E' (c*B) 1:={
    rate:=zero_le_one
    safe:=hb.trans hvB
    samples:=fun i a k hh=>(Dyad.pure (by norm_num) hb (permit_ready (hN i).inlet).coherent (hB.after0 i a k hh).near).mono hvB
    pulse:=by
       intro i hp a k hk
       have hv0:|tap k (E' a i)|≤c*B:=by
          obtain h|⟨rfl,h⟩:=hk;exact (hB.currency k _ _ h).1.trans hvB;exact (hV i a hp h).1
       exact ⟨hv0,hv0,by rw [sub_self,abs_zero,mul_one];exact hb.trans hvB⟩}
 have h1':Candor (D:=D) hf.coarse X e l n N' N' E'' E'' (c*B) 1:={
    rate:=zero_le_one
    safe:=hb.trans hvB
    samples:=fun i a k hh=>(Dyad.pure (by norm_num) hb (permit_ready (hN' i).inlet).coherent (hB.after0 i a k hh).far).mono hvB
    pulse:=by
       intro i hp a k hk
       have hv0:|tap k (E'' a i)|≤c*B:=by
          obtain h|⟨rfl,h⟩:=hk;exact (hB.currency k _ _ h).2.1.trans hvB;exact (hV i a hp h).2.1
       exact ⟨hv0,hv0,by rw [sub_self,abs_zero,mul_one];exact hb.trans hvB⟩}
 let γ(W:ℝ):=u*A*W/g + u*(m*(B+1)+y*(c*B)*(c*B))
 have hV0:=answer X (zero_le_one.trans hC) hR.tasked hCl hR.wins hR.unique0 hN h0' ha hB0 (mul_nonneg (zero_le_one.trans hm) (by linarith)) (fun i hi=>(hJe i hi).1)
 have hV1:=answer X (zero_le_one.trans hC) hR'.tasked hCr hR'.wins hR'.unique0 hN' h1' ha hB1 (mul_nonneg (zero_le_one.trans hm) (by linarith)) (fun i hi=>(hJe i hi).2.1)
 have hV0(i:I₀)(hi:octave i=l):Sings Δ D hf.coarse (N i e n) (γ B0):=by convert hV0 i hi using 1;unfold γ u m y c;ring
 have hV1(i:I₀)(hi:octave i=l):Sings Δ D hf.coarse (N' i e n) (γ B1):=by convert hV1 i hi using 1;unfold γ u m y c;ring
 have hmp0:0 ≤ m:=zero_le_one.trans hm
 have hhQ:8*(A+u+y+Ic+m+c)≤f:=by unfold f w v c m;linarith only
 obtain ⟨hγs,hIburst,hfc',hfp⟩:=bills A B c y m u Ic B1 f g hA hb' hc1 hy hm hU hIc hB1 (Nat.one_le_cast.mpr P.L.property) hf' hhQ
 have hC'a: u*A ≤ C':=le_add_of_nonneg_left zero_le_one
 have hZ(V:ℝ)(ht:0≤V):γ V≤C'*V/g+q W*B^2:= (hγs V).trans (add_le_add (by gcongr) le_rfl)
 let G':=c*(B+B1);have ht':c*B ≤ G':=by unfold G'; nlinarith only [hB1,hc1]
 have Hδ:Candor (D:=D) hf.coarse X e l n N N' E' E'' G' δ:={
    rate:=hδ.le
    safe:=hb.trans (hvB.trans ht')
    samples:=fun i a k hh=>(hB.after0 i a k hh).mono (hvB.trans ht')
    pulse:=by
       intro i hp a k hk
       obtain hk|⟨rfl,hk⟩:=hk
       · obtain ⟨h₁,h₂,h₃⟩:=hB.currency k i a hk -- order i a? hB.currency a i j. yes
         exact ⟨h₁.trans (hvB.trans ht'),h₂.trans (hvB.trans ht'),h₃.trans (mul_le_mul_of_nonneg_right (hvB.trans ht') hδ.le)⟩
       obtain ⟨h₁,h₂,h₃⟩:=hV _ _ hp hk
       exact ⟨h₁.trans ht',h₂.trans ht',h₃⟩}
 have hhγ : 0 ≤ γ B1 := by
   have hcb : 0 ≤ c * B := mul_nonneg (zero_le_one.trans hc1) hb
   exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg hU (zero_le_one.trans hA)) hB1) hg.le)
     (mul_nonneg hU (add_nonneg (mul_nonneg hmp0 (add_nonneg hb zero_le_one))
       (mul_nonneg (mul_nonneg hy hcb) hcb)))
 have hΔ:=answer_delta X (zero_le_one.trans hC) hR.tasked hCl hCr hR.unique0 hR'.unique0 hN hN' Hδ ha hT (mul_nonneg hmp0 (by positivity)) hn (fun i hi=>(hJe i hi).2.2) hhγ hV1
 let x:= B+B1;have hx':1 ≤ x:= by unfold x; linarith only [hb',hB1]
 have hqu:(0:ℝ)≤ q W:=by unfold q; positivity
 have hiBurst:u*(m*x+ Ic*((e:ℝ)+2)*(2*G'*G')+Ic*G'*γ B1) ≤ f^10*x^4:=by
    convert hIburst using 1; unfold γ y x G'; ring_nf
 have hj(i:I₀)(hi:octave i=l):Sings Δ D hf.coarse (N i e n-N' i e n) (C'*T/g+q W*x^4*δ):=by
    refine (hΔ i hi).mono le_rfl le_rfl (fun _=>le_rfl) (add_le_add (by change u*A*T/g ≤ _;gcongr) (mul_le_mul_of_nonneg_right hiBurst hδ.le))
 refine ⟨fun i hi=>by obtain hi:= (booth_in X|>.mp hi);exact ⟨(hV0 i hi).mono le_rfl le_rfl (fun _=>le_rfl) (hZ _ hB0),(hV1 i hi).mono le_rfl le_rfl (fun _=>le_rfl) (hZ _ hB1)⟩,fun i hi=>hj i ((booth_in X).mp hi), ?_,?_⟩
 · have h:c*B≤ q W*B^2:=mul_le_mul hfc' (by nlinarith only [hb']) hb hqu
   exact ⟨⟨fun i j hi hh=>(hV i j hi hh).1.trans h⟩,⟨fun i j hi hh=>(hV i j hi hh).2.1.trans h⟩⟩
 refine ⟨fun i j hi hh=>?_⟩
 rw [dusk_diff];change |tap e (E' j i)-tap e (E'' j i)|≤_
 apply (hV i j hi hh).2.2.trans
 unfold q;change c*x*δ≤ f^10*x^4*δ; apply mul_le_mul_of_nonneg_right (mul_le_mul hfc' (le_self_pow₀ hx' (by norm_num)) (by linarith only [hx']) (by positivity)) hδ.le

end YM.RG08.Sideshow

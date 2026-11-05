import YM.TraceExtension.Zn.Largish
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {F:ℝ→ℝ}{a b c:ℝ}{k:ℕ}{G:Gauge}{n:Side}
lemma stays(k:ℕ): Tigh (fun x=> (x^k)⁻¹) k:= (eventually_gt_atTop (0:ℝ)).mono fun x hx=>⟨by positivity,le_rfl⟩
lemma balloon: ConstMass 0 (fun x=> (puff x:ℝ)):=by unfold puff; push_cast; exact (((rim_S.gather (mass (by norm_num))).gather (mass (by norm_num))).times _ (by norm_num))
lemma expansion: ConstMass 0 (fun x=> (high x:ℝ)):=by unfold Zn.high; push_cast; exact ((upperB.gather rim_S).times (1800:ℝ) (by norm_num)).gather balloon
lemma post(k:ℕ) {G:Gauge} {n:Side} (F:Peat G n) (A a b c:ℝ)(Q:Support n)(ha: c ≤ b)(hf: Splendor F Q k a b)(hp:a≤ A) : Splendor F Q k A c:= ⟨hf.cloth,hf.locale,hf.symm,hf.lit,fun V _ _ W y hv=> ((hf.tickets V W y fun i=> (hv i).mono ha)).mono hp⟩
lemma mot(k:ℕ) {G:Gauge}{n:Side}(F:Peat G n)(A a b c:ℝ)(Q:Support n)(ha:c≤ b)(hf:HearthV F Q k a b)(hp:a≤ A): HearthV F Q k A c:=⟨hf.silk,hf.pillar,hf.symU,hf.choir,fun V _ _ W y hv=> (hf.price V W y fun i=>(hv i).mono ha).mono hp⟩
abbrev mew(x:ℝ):= Wave (1/2000) x
lemma follower {G:Gauge}{n:Side}(F:Gal G n)(k:ℕ)(A a b c:ℝ)(ha:c≤b)(h: Climate F k a b)(hp:a ≤ A):Climate F k A c:=⟨fun V _ _ W y H i=> (h.laps V W y (fun j=> (H j).mono ha) i).mono hp⟩
lemma cloche(G:Gauge)(A:ℝ)(ha:0 ≤ A)(k:ℕ):∀ᶠ x:ℝ in atTop,∀ (n:Side)(J:Dart G n)(R:Rep G n),Sight x R J→ (∀ b:G.ColorIndex, |midPay b J - (Holt b (fun i=> stubJ (lush (YCore x J i)) ∘ input G n)).re| ≤ calorie x) ∧
    ∀ i:Axis,∀ (V:Type)[NormedAddCommGroup V][NormedSpace ℝ V](U:V→ Config G n)(v:V), (∀ e, Allows (k+1) (fun y=> G.mat (U y e)) v A) → Allows k (lush (YCore x J i) ∘ U) v (thinM x):=by
    obtain ⟨C,D,hC,hD,H⟩:= Xo.forever G; obtain ⟨E,hE,hP⟩:= Xo.lushLine G k A ha
    let f(x):= (eastD x)/5/4/5
    let g(x):=D*(ramt 3 (Fin 2) (f x)+ramt 2 (Fin 2) (f x))*(C*tightf x*countCost (f x)); have hg:Tigh g 67:=by
        have he(x): f x= Perfect.east x/(100*5*4*5):=by unfold f eastD; simp_rw [div_div]
        unfold g; simp_rw [he]; exact (((stays 70).fact C hC).fly (priced (D:=100*5*4*5) (by norm_num))).mult ((ConstMass.gather (rimt 3 _ (by norm_num)) (rimt 2 _ (by norm_num))).times D hD)
    let m(x):= (((puff x+puff x+1)^4:ℕ)* Fintype.card (Loc G 1) :ℕ)*(mew x); have hm: ConstMass (1/2000) m:=by
       unfold m; push_cast; have hr:=(waveM (1/2000:ℝ)); refine ?_
       simpa only[zero_add] using! (((((balloon.gather balloon).gather (mass (show (0:ℝ) ≤ 1 by norm_num))).crop 4).cop (mass (show 0 ≤ (Fintype.card (Loc G 1):ℝ) by positivity))).prod hr)
    filter_upwards [hg.tight (show 30≤67 by omega),weather G E hE k (1/2000) (by norm_num),hm (1/200) (by norm_num),eastP,eventually_gt_atTop (0:ℝ)] with x hx hv hz he hX n J R h
    have h'(i:Axis):= hv n J R h i
    constructor
    · intro b; have h0:0 ≤ tightf x:=by unfold tightf; positivity
      exact (H n (fun i=> J.Y i 0) (YCore x J) (fun i=> ⟨h.1.sound.palm ..,(h' i).1.rises⟩) (eastD x) _ (div_pos he.1 (by norm_num)) h0 (fun i=>(h' i).2.2.1) b).trans hx.2
    intro i V _ _ U v H; refine (hP V n (YCore x J i) _ _ U v (h' i).1 (h' i|>.2.1) H).mono ((le_trans ?_ hz.2))
    apply mul_le_mul_of_nonneg_right _ (wake ..).le; apply Nat.cast_le.mpr
    gcongr; exact (Corona.halo_size ..).trans (by simp)
lemma adriftR{n:Side}(U:Rep G n)(x:ℝ)(S:Stage)(h:Made S x U): salo U (puff x) (rim x)=high x:=by unfold salo; rw[h.2.1];rfl
lemma h_mass : ConstMass (1/1000) humble:=by have h:= (waveM (1/1000)).times 2 zero_le_two; change ConstMass _ (fun x=> Wave (1/1000) x*2); simpa only [mul_comm (2:ℝ)] using h
end YM.Trace.Zn

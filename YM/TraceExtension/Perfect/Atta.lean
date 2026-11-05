import YM.TraceExtension.Perfect.Mori
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {P:Patch}{Z:KernelChoices}{p:Clip}{G:Gauge}{μ A α B D H u v C:ℝ}{f:Side} {V:Type}{F:Filter V}
set_option quotPrecheck false
variable {X: V→ Slide G P Z p μ A α B} (h : LotFee F X u v H D)
local notation "F!"=>fun w=>(X w).f
local notation "C!"=>fun w=>(X w).c
variable (X)
def tours (J:∀ w,Site (X w).f→Peat G (X w).f) (w:V)(x:Site (X w).f) := ballX (inheritJ (X w).wood (X w).ρ (J w x))
def turns (Y:∀ w,Site (X w).f→Gal G (X w).f) (w:V)(x:Site (X w).f) := bottom (inheritY (X w).wood (X w).ρ (X w).t (Y w x))
variable {X} {J:∀ w:V,Site (X w).f→Peat G (X w).f}{K:∀ w:V,Site (X w).f→Gal G (X w).f} {k:ℕ}
lemma tourS (hx:∀ w x,J w x∈loom G (X w).f): Tour X (fun w x=> ballX (J w x)) (tours X J):= by
 refine ⟨fun w x=>(loom_read (hx w x)).2.2,fun w x=>(loom_read (hx w x)).2.1,fun w x=>?_,fun w x=>?_⟩
 · obtain ⟨h,_⟩:=hx w x; exact inn_letter h (X w).law (X w).t x
 obtain ⟨h,_⟩:=hx w x; exact moonset h (X w).law (X w).t
lemma tourY (hx:∀ w x,K w x∈rains G (X w).f): Tour X (fun w x=>bottom (K w x)) (turns X K):= by
 refine ⟨fun w x=>(rain_read (hx w x)).2.2.1,fun w x=>(rain_read (hx w x)).2.1,fun w x=> ?_,fun w x=>?_⟩
 · obtain ⟨h,_⟩:= hx w x; exact grants_pin (X w).t (X w).law (X w).size.1 x (X w).price _ h
 obtain ⟨h,_⟩:= hx w x; exact mantle (X w).law (X w).size.1 (X w).t (X w).price h
variable (x:∀ w, Site (X w).c)
lemma drips (S:Sheaf)(w:V)(j:ℕ) : ballX (Dart.hum (X w).wood (X w).ρ P.L S j (J w) (x w))=Tour.ill X (tours X J) j S w (x w):=by
   let r:=(X w).s.ratio; let A:= (P.L.val:ℝ); let K := inheritJ (X w).wood (X w).ρ ∘ J w
   change topF (A^j • verse S r K (x w))= _; rw [map_smul,show topF _=_ from congr_fun (verse_map topF K r S) (x w)]; rfl
lemma dropY (S:Sheaf)(w:V) : bottom (Dart.mel (X w).wood (X w).ρ (X w).t P.L S (K w) (x w))=Tour.ill X (turns X K) 5 S w (x w):=by
 let r:=(X w).s.ratio; let A:= (P.L.val:ℝ); let J := inheritY (X w).wood (X w).ρ (X w).t ∘ K w
 change follic (A^5 • verse S r J (x w))=_; rw[map_smul,show follic _=_ from congr_fun (verse_map follic J r S) (x w)]; rfl

local notation "LX"=> (P.L.val:ℝ)
local notation "cₗ"=> (2:ℝ)^13*H^2
local notation "Sₗ"=> Tour.allSheaf

structure Bank (H D:ℝ)(L:Side)(W:ℝ)(d f e E:ℕ→ℝ) : Prop where
 maj i : 0 ≤ d i
 piv i : 0 ≤ f i
 J : 3*(Tour.allSheaf*(2^13*H^2*(W+(d 2+W)/(L.val:ℝ)))) ≤ f 2
 Q : 3*(Tour.allSheaf*2^13*H^2/(L.val:ℝ)* d 2) ≤ f 2
 epos i : 0 ≤ e i
 Epos i : 0 ≤ E i
 elm : Tour.allSheaf*(2^13*H^2)/(L.val:ℝ) * e 2≤ E 2
 tall i : 2 < i→ i≤4→ 3*((L.val:ℝ)^5*Tour.allSheaf*(((2*H/(L.val:ℝ)^2)^i*d i)+ ∑ z∈univ.erase (OrderedFinpartition.atomic i), D^z.length*d z.length))≤ f i
 scarf i : 2 < i→ i≤4→ ((L.val:ℝ)^5*Tour.allSheaf*(((2*H/(L.val:ℝ)^2)^i*e i)+ ∑ z∈univ.erase (OrderedFinpartition.atomic i), D^z.length*e z.length))≤ E i
variable {W:ℝ}{d f' e E:ℕ→ℝ}(hW:0 ≤ W)(hb: Bank H D P.L W d f' e E)
include h hb
lemma wind (V:Tit G→Tit G→ℝ)(hp:Tour X (fun w x=>ballX (J w x)) (tours X J)) (hP:∀ x,Tip F x (fun w=>ballX (J w (x w))) V 4)
   {J'}(hS:Tour X (fun w x=>ballX (J' w x)) (tours X J'))(h':∀ x,Tip F x (fun w=>ballX (J' w (x w))) V 4)
   (hf:∀ x,Ear F x (fun w=>ballX (J' w (x w))) v 2 W)(hj:∀ x,Ear F x (fun w=>ballX (J w (x w))) v 2 (d 2)) (S:Sheaf)(hs:S.radius ≤ 140*P.L.val)(he:S.debt ≤ Sₗ):
   0≤ W→ Ear F x (fun w=>Tour.ill X (tours X J) 4 S w (x w)) u 2 (f' 2/3):=by
 intro hW
 have hx:=Tour.boolJ h hp V hP hS h' W (d 2) hW (hb.maj 2) hf hj x
 have hL:LX>0:= side_pos _; have hD:=hb.maj 2
 apply (Tour.bill 4 _ _ hs he _ (by positivity) x hx).up
 calc
   _ = Sₗ*(2^13*H^2*(W+(d 2+W)/LX)):=by field_simp
   _ ≤ _:=by linarith only [hb.J]
lemma windY (V:Tit G→Tit G→ℝ)(hU:∀ i j,ScoreG i+ScoreG j<5 → V i j=0)(hp:Tour X (fun w x=>bottom (K w x)) (turns X K))(hP:∀ x,Tip F x (fun w=>bottom (K w (x w))) V 5)
   {J'}(hS:Tour X (fun w x=>bottom (J' w x)) (turns X J'))(h':∀ x,Tip F x (fun w=>bottom (J' w (x w))) V 5)
   (hf:∀ x,Ear F x (fun w=>bottom (J' w (x w))) v 2 W)(hj:∀ x,Ear F x (fun w=>bottom (K w (x w))) v 2 (d 2))(S:Sheaf)(hs:S.radius ≤ 140*P.L.val)(he:S.debt ≤ Sₗ):
   0≤ W→Ear F x (fun w=>Tour.ill X (turns X K) 5 S w (x w)) u 2 (f' 2/3):=by
 intro hW
 have hx:=Tour.boolY h hp V hU hP hS h' W (d 2) hW (hb.maj 2) hf hj x
 have hL:LX>0:= side_pos _; have hD:=hb.maj 2
 apply (Tour.bill 5 _ _ hs he _ (by positivity) x hx).up
 calc
   _ = Sₗ*(2^13*H^2*(W+(d 2+W)/LX)):=by field_simp
   _ ≤ _:=by linarith only [hb.J]
lemma windQ (hp:Tour X (fun w x=>ballX (J w x)) (tours X J))(hh:∀ x,Ear F x (fun w=>ballX (J w (x w))) v 2 (d 2))(S:Sheaf)(hs:S.radius≤140*P.L.val)(he:S.debt≤ Sₗ) : Ear F x (fun w=>Tour.ill X (tours X J) 3 S w (x w)) u 2 (f' 2/3) :=by
 have hL:LX>0:=side_pos _; have hx:=hb.maj 2
 apply (Tour.bill 3 _ _ hs he _ (by positivity) x (fun q hq=> Tour.lvl2 h hp _ hx hh x q hq)).up
 calc
   _ = Sₗ*2^13*H^2/LX *d 2:=by field_simp
   _ ≤ _:=by linarith only[hb.Q]
lemma windE (hp:Tour X (fun w x=>ballX (J w x)) (tours X J))(hh:∀ x,Ear F x (fun w=>ballX (J w (x w))) v 2 (e 2))(hv:∀ x,Tip F x (fun w=> ballX (J w (x w))) 0 5)(S:Sheaf)(hs:S.radius≤140*P.L.val)(he:S.debt ≤ Sₗ):
   Ear F x (fun w=>Tour.ill X (tours X J) 5 S w (x w)) u 2 (E 2):=by
 have hL:LX>0:=side_pos _; have hx:= hb.epos 2; apply (Tour.bill 5 _ _ hs he _ (by positivity) x (fun q hq=> Tour.boar h hp x q hq (hh _) (hv _))).up
 apply le_trans _ hb.elm
 field_simp
 have hz:=Tour.sheaf_debt_pos; nlinarith only[hx,hz,sq_nonneg H, mul_nonneg (mul_nonneg (sq_nonneg H) hz.le) hx]
lemma windB {U:∀ w,Site (X w).f→Acr G (X w).f→ℝ}{V':∀ w,Site (X w).f→Acr G (X w).c→ℝ}(hp:Tour X U V')(n:ℕ)(h₀: 2 < n)(hn:n≤4)(g:ℕ)(hg:g≤5)(S:Sheaf)(hs:S.radius ≤ 140*P.L.val)(he:S.debt ≤ Sₗ):
    ( (∀ x i,i ≤ n→2 ≤ i→ Ear F x (fun w=> U w (x w)) v i (d i)) → Ear F x (fun w=>Tour.ill X V' g S w (x w)) u n (f' n/3)) ∧
    ((∀ x i,i ≤ n→2 ≤ i→ Ear F x (fun w=> U w (x w)) v i (e i)) → Ear F x (fun w=>Tour.ill X V' g S w (x w)) u n (E n)):=by
 have hh (X':ℕ→ℝ)(hx:∀ i,0 ≤ X' i)(hU:∀ x i,i ≤ n→2 ≤ i→Ear F x (fun w=>U w (x w)) v i (X' i)): Ear F x (fun w=>Tour.ill X V' g S w (x w)) u n (LX^5*Sₗ*(((2*H/LX^2)^n*X' n)+ ∑ z∈univ.erase (OrderedFinpartition.atomic n), D^z.length*X' z.length)):=by
     have hL : 1≤LX:=by exact_mod_cast P.L.property
     have hV:= Tour.sheaf_debt_pos; have hc:0 ≤ D:= h.sum.2.2.2.2.2.2; have hz:0 ≤ H:= h.sum.2.2.2.2.2.1
     have hv:0≤ ((2*H/LX^2)^n*X' n)+ ∑ z∈univ.erase (OrderedFinpartition.atomic n), D^z.length*X' z.length:= add_nonneg (mul_nonneg (by positivity) (hx _)) (Finset.sum_nonneg fun i _=> mul_nonneg (pow_nonneg hc _) (hx _))
     have ha:= Tour.bill g n S hs he _ hv x (fun q hq=>hp.boon h _ q hq n h₀.le hn X' hx (hU _))
     refine ha.up (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hg) hV.le) hv)
 constructor
 · intro h; apply (hh d hb.maj h).up; linarith only[hb.tall n h₀ hn]
 intro h; exact (hh e hb.epos h).up (hb.scarf n h₀ hn)
end YM.Trace.Perfect
